use std::cell::UnsafeCell;
use std::fmt::Display;
use std::iter::Iterator;
use regex::Regex;

use nom::InputLength;

use crate::error::{Tagged, SyntaxError, Syntax, SyntaxElement, Position};
use crate::traits::Taggable;


/// Result type for calls to the lexer: either a new lexer and a token, or a syntax error.
pub(crate) type LexResult<'a> = Result<(Lexer<'a>, Tagged<Token<'a>>), SyntaxError>;
pub(crate) type CachedLexResult<'a> = Result<(CachedLexer<'a>, Tagged<Token<'a>>), SyntaxError>;


/// To speed up lexing, the result from the last call is saved.
type LexCache<'a> = UnsafeCell<Option<(Ctx, usize, LexResult<'a>)>>;


/// Complete list of all token types in the Gold grammar.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum TokenType {
    Arrow,              // ->
    Asterisk,           // *
    Caret,              // ^
    CloseAngle,         // >
    CloseBrace,         // }
    CloseBracePipe,     // |}
    CloseBracket,       // ]
    CloseParen,         // )
    Colon,              // :
    Comma,              // ,
    Dollar,             // $
    Dot,                // .
    DoubleColon,        // ::
    DoubleEq,           // ==
    DoubleSlash,        // //
    DoubleQuote,        // "
    Ellipsis,           // ...
    Eq,                 // =
    ExclamEq,           // !=
    GreaterEq,          // >=
    Ampersand,          // &
    LessEq,             // <=
    Minus,              // -
    OpenAngle,          // <
    OpenBrace,          // {
    OpenBracePipe,      // {|
    OpenBracket,        // [
    OpenParen,          // (
    Pipe,               // |
    Plus,               // +
    SemiColon,          // ;
    Slash,              // /

    Name,               // Identifier
    Float,              // Floating point number
    Integer,            // Integer
    StringLit,          // String literal
    MultiString,        // Multiple-line string literal
}


/// Enumeration of all possible token contexts.
///
/// Tokenization of the Gold language is ever so slightly context-dependent. The
/// lexer does not keep track of the information necessary to determine the
/// context: that falls to the parser.
#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) enum Ctx {
    /// Default context (normal code)
    Default,

    /// String context (after an opening double quote)
    String,

    /// Map context (allows for relaxed conditions on map keys as opposed to identifiers)
    Map,

    /// Multiple-line string context (after double colon in map context)
    MultiString(u32),
}


impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Arrow => "'->'",
            Self::Asterisk => "'*'",
            Self::Caret => "'^'",
            Self::CloseBrace => "'}'",
            Self::CloseBracePipe => "'|}'",
            Self::CloseBracket => "']'",
            Self::CloseParen => "')'",
            Self::Colon => "':'",
            Self::Comma => "','",
            Self::Dollar => "'$'",
            Self::Dot => "'.'",
            Self::DoubleColon => "'::'",
            Self::DoubleEq => "'=='",
            Self::DoubleSlash => "'//'",
            Self::DoubleQuote => "'\"'",
            Self::Ellipsis => "'...'",
            Self::Eq => "'='",
            Self::ExclamEq => "'!='",
            Self::CloseAngle => "'>'",
            Self::GreaterEq => "'>='",
            Self::OpenAngle => "'<'",
            Self::LessEq => "'<='",
            Self::Minus => "'-'",
            Self::OpenBrace => "'{'",
            Self::OpenBracePipe => "'{|'",
            Self::OpenBracket => "'['",
            Self::OpenParen => "'('",
            Self::Pipe => "'|'",
            Self::Plus => "'+'",
            Self::SemiColon => "';'",
            Self::Slash => "'/'",
            Self::Ampersand => "'&'",
            Self::Name => "name",
            Self::Float => "float",
            Self::Integer => "int",
            Self::StringLit => "string literal",
            Self::MultiString => "multi-line string literal",
        })
    }
}


/// A token has a type and a reference to the slice of the input buffer that generated it.
#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) struct Token<'a> {
    pub kind: TokenType,
    pub text: &'a str,
}


/// A lexer, for tokenizing a string of code.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Lexer<'a> {
    code: &'a str,
    position: Position,
}


lazy_static! {
    // Regex for skipping whitespace (not including EOL)
    static ref WHITESPACE: Regex = Regex::new(r"^[^\S\n]*").unwrap();

    // Regex for matching a valid identifier
    static ref NAME: Regex = Regex::new("^[[:alpha:]_][^\\s'\"{}()\\[\\]/+*\\-;:,.=#\\|^<>]*").unwrap();

    // Regex for matching a valid map key
    static ref KEY: Regex = Regex::new("^[^\\s'\"{}()\\[\\]:]+").unwrap();

    // Floating point variant a: integer followed by dot, optional fractional part and optional exponent
    static ref FLOAT_A: Regex = Regex::new(r"^[[:digit:]][[:digit:]_]*\.[[:digit:]_]*(?:(?:e|E)(?:\+|-)?[[:digit:]][[:digit:]_]*)?").unwrap();

    // Floating point variant b: dot followed by fractional part and optional exponent
    static ref FLOAT_B: Regex = Regex::new(r"^\.[[:digit:]][[:digit:]_]*(?:(?:e|E)[[:digit:]][[:digit:]_]*)?").unwrap();

    // Floating point variant c: integer followed by exponent
    static ref FLOAT_C: Regex = Regex::new(r"^[[:digit:]][[:digit:]_]*(?:e|E)(?:\+|-)?[[:digit:]][[:digit:]_]*").unwrap();

    // Regex for matching an integer
    static ref DIGITS: Regex = Regex::new("^[[:digit:]][[:digit:]_]*").unwrap();
}


impl<'a> Lexer<'a> {
    /// Construct a new lexer.
    pub fn new(code: &'a str) -> Lexer<'a> {
        Lexer {
            code,
            position: Position::zero(),
        }
    }

    /// Return the current position of the lexer.
    pub fn position(&self) -> Position {
        self.position
    }

    /// Construct a cache cell that can be used to make a cached lexer.
    pub fn cache() -> LexCache<'a> {
        UnsafeCell::default()
    }

    /// Construct a cached lexer with an existing cache cell.
    pub fn with_cache(self, cache: &'a LexCache<'a>) -> CachedLexer<'a> {
        CachedLexer::new(self, cache)
    }

    /// Peek the next character.
    fn peek(&self) -> Option<char> {
        self.code.chars().next()
    }

    /// Return true if the i'th character exists and satisfies the predicate `f`.
    fn satisfies_at(&self, i: usize, f: impl FnOnce(char) -> bool) -> bool {
        self.code.chars().nth(i).is_some_and(f)
    }

    /// Advance the lexer in the buffer.
    ///
    /// This method is subject to the same restrictions as [`Position::adjust`].
    fn skip(self, offset: usize, delta_line: u32) -> Self {
        Lexer {
            code: &self.code[offset..],
            position: self.position.adjust(offset, delta_line)
        }
    }

    /// Advance the lexer in the buffer and return a result consisting of the
    /// new lexer and a token.
    ///
    /// This will never return an error variant. It's wrapped in `Ok()` for
    /// utility since it will be called from tail position in other methods that
    /// may return errors.
    fn skip_tag(self, offset: usize, delta_line: u32, kind: TokenType) -> LexResult<'a> {
        let code = self.code[..offset].tag(self.position.with_length(offset));
        Ok((self.skip(offset, delta_line), code.map(|span| Token { kind, text: span })))
    }

    /// Traverse over the match of a regular expression and return a token.
    ///
    /// The regex must never match beyond the first character.
    fn traverse(self, regex: &'a Regex, element: SyntaxElement, kind: TokenType) -> LexResult<'a> {
        regex.find(self.code).map(|m| {
            let lex = self.skip(m.start(), 0);
            lex.skip_tag(m.end() - m.start(), 0, kind).unwrap()
        }).ok_or_else(|| self.error(Syntax::from(element)))
    }

    /// Skip an arbitrary amount of whitespace (including comments and newlines).
    pub fn skip_whitespace(mut self) -> Self {
        loop {
            self = self.skip_indent();

            match self.peek() {
                Some('\n') => {
                    self = self.skip(1, 1);
                    continue;
                },
                Some('#') => {
                    let end = self.code.find('\n').unwrap_or(self.code.len() - 1);
                    self = self.skip(end + 1, 1);
                },
                _ => {
                    break;
                },
            }
        }

        self
    }

    /// Skip whitespace at the beginning of a line. Will not skip comments or
    /// newlines.
    fn skip_indent(self) -> Self {
        // The WHITESPACE regex cannot fail to match, so unwrapping is safe
        WHITESPACE.find(self.code).map(|m| self.skip(m.end(), 0)).unwrap()
    }

    /// Interpret the next token as a number (integer or float) and return it.
    fn next_number(self) -> LexResult<'a> {
        self.traverse(&FLOAT_A, SyntaxElement::Number, TokenType::Float)
        .or_else(|_| self.traverse(&FLOAT_B, SyntaxElement::Number, TokenType::Float))
        .or_else(|_| self.traverse(&FLOAT_C, SyntaxElement::Number, TokenType::Float))
        .or_else(|_| self.traverse(&DIGITS, SyntaxElement::Number, TokenType::Integer))
    }

    /// Interpret the next token as an identifier and return it.
    fn next_name(self, regex: &'a Regex) -> LexResult<'a> {
        self.traverse(regex, SyntaxElement::Identifier, TokenType::Name)
    }

    /// Return an error at the current location.
    pub fn error(&self, reason: Syntax) -> SyntaxError {
        SyntaxError::new(self.position, Some(reason))
    }

    /// Return the next token. Will look up the cached result and return it if
    /// appropriate, or calculate a new token and set the cache.
    pub fn next(self, ctx: Ctx, cache: &LexCache<'a>) -> LexResult<'a> {
        // Check if the cache is set and matches
        if let Some((tok_ctx, tok_offset, result)) = unsafe { &*cache.get() } {
            if tok_ctx == &ctx && tok_offset == &self.position.offset() {
                return *result;
            }
        }

        // Dispatch to the appropriate submethod
        let result = match ctx {
            Ctx::Default => self.tokenize_default(),
            Ctx::Map => self.tokenize_map(),
            Ctx::String => self.tokenize_string(),
            Ctx::MultiString(col) => self.tokenize_multistring(col),
        };

        // Set the cache and return
        unsafe { *cache.get() = Some((ctx, self.position.offset(), result)); }
        result
    }

    /// Return the next token in the default context.
    fn tokenize_default(mut self) -> LexResult<'a> {
        // Gold is 100% whitespace insensitive in the default context.
        self = self.skip_whitespace();

        match self.peek() {
            // Identifiers begin with letters or underscores
            Some('a'..='z') | Some('A'..='Z') | Some('_') => self.next_name(&NAME),

            // A digit, or a dot followed by a digit signifies a number
            Some(x) if x.is_ascii_digit() => self.next_number(),
            Some('.') if self.satisfies_at(1, |x| x.is_ascii_digit()) => self.next_number(),

            // Other tokens. Note that specific cases must be checked before
            // general ones! I.e., check for '::' before ':'.
            Some('.') if self.satisfies_at(1, |x| x == '.') && self.satisfies_at(2, |x| x == '.') => self.skip_tag(3, 0, TokenType::Ellipsis),
            Some('.') => self.skip_tag(1, 0, TokenType::Dot),
            Some(':') if self.satisfies_at(1, |x| x == ':') => self.skip_tag(2, 0, TokenType::DoubleColon),
            Some(':') => self.skip_tag(1, 0, TokenType::Colon),
            Some('"') => self.skip_tag(1, 0, TokenType::DoubleQuote),
            Some('{') if self.satisfies_at(1, |x| x == '|') => self.skip_tag(2, 0, TokenType::OpenBracePipe),
            Some('{') => self.skip_tag(1, 0, TokenType::OpenBrace),
            Some('|') if self.satisfies_at(1, |x| x == '}') => self.skip_tag(2, 0, TokenType::CloseBracePipe),
            Some('}') => self.skip_tag(1, 0, TokenType::CloseBrace),
            Some('[') => self.skip_tag(1, 0, TokenType::OpenBracket),
            Some(']') => self.skip_tag(1, 0, TokenType::CloseBracket),
            Some('(') => self.skip_tag(1, 0, TokenType::OpenParen),
            Some(')') => self.skip_tag(1, 0, TokenType::CloseParen),
            Some(',') => self.skip_tag(1, 0, TokenType::Comma),
            Some('+') => self.skip_tag(1, 0, TokenType::Plus),
            Some('-') if self.satisfies_at(1, |x| x == '>') => self.skip_tag(2, 0, TokenType::Arrow),
            Some('-') => self.skip_tag(1, 0, TokenType::Minus),
            Some('/') if self.satisfies_at(1, |x| x == '/') => self.skip_tag(2, 0, TokenType::DoubleSlash),
            Some('/') => self.skip_tag(1, 0, TokenType::Slash),
            Some('*') => self.skip_tag(1, 0, TokenType::Asterisk),
            Some('^') => self.skip_tag(1, 0, TokenType::Caret),
            Some('<') if self.satisfies_at(1, |x| x == '=') => self.skip_tag(2, 0, TokenType::LessEq),
            Some('<') => self.skip_tag(1, 0, TokenType::OpenAngle),
            Some('>') if self.satisfies_at(1, |x| x == '=') => self.skip_tag(2, 0, TokenType::GreaterEq),
            Some('>') => self.skip_tag(1, 0, TokenType::CloseAngle),
            Some('=') if self.satisfies_at(1, |x| x == '=') => self.skip_tag(2, 0, TokenType::DoubleEq),
            Some('=') => self.skip_tag(1, 0, TokenType::Eq),
            Some('!') if self.satisfies_at(1, |x| x == '=') => self.skip_tag(2, 0, TokenType::ExclamEq),
            Some('|') => self.skip_tag(1, 0, TokenType::Pipe),
            Some(';') => self.skip_tag(1, 0, TokenType::SemiColon),
            Some('&') => self.skip_tag(1, 0, TokenType::Ampersand),

            // Error conditions
            Some(c) => Err(self.error(Syntax::UnexpectedChar(c))),
            None => Err(self.error(Syntax::UnexpectedEof)),
        }
    }

    /// Return the next token in the map context.
    fn tokenize_map(mut self) -> LexResult<'a> {
        self = self.skip_whitespace();

        match self.peek() {
            Some('}') => self.skip_tag(1, 0, TokenType::CloseBrace),
            Some('$') => self.skip_tag(1, 0, TokenType::Dollar),
            Some('"') => self.skip_tag(1, 0, TokenType::DoubleQuote),
            Some(':') if self.satisfies_at(1, |x| x == ':') => self.skip_tag(2, 0, TokenType::DoubleColon),
            Some(':') => self.skip_tag(1, 0, TokenType::Colon),
            Some('.') if self.satisfies_at(1, |x| x == '.') && self.satisfies_at(2, |x| x == '.') => self.skip_tag(3, 0, TokenType::Ellipsis),
            Some(_) => self.next_name(&KEY),
            None => Err(self.error(Syntax::UnexpectedEof)),
        }
    }

    /// Return the next multi-line string token, interrupted on the first line
    /// whose indentation is not greater than `col`.
    fn tokenize_multistring(mut self, col: u32) -> LexResult<'a> {
        let orig = self;

        // The string always spans to at least the first newline.
        let end = self.code.find('\n').unwrap_or(self.code.len() - 1);
        self = self.skip(end + 1, 1);

        loop {
            // Break if this line has indentation not greater than `col`.
            let skipped = self.skip_indent();
            if skipped.position.column() <= col {
                break;
            }

            // Advance the position to the next line.
            let end = skipped.code.find('\n').unwrap_or(self.code.len() - 1);
            self = skipped.skip(end + 1, 1);
        }

        // Construct a token for the span that has been traversed.
        let span = self.position - orig.position;
        let tok = Token {
            kind: TokenType::MultiString,
            text: &orig.code[..span.length()],
        }.tag(span);

        Ok((self, tok))
    }

    /// Return the next token in a string context.
    fn tokenize_string(self) -> LexResult<'a> {
        match self.peek() {
            None => Err(self.error(Syntax::UnexpectedEof)),

            Some('"') => self.skip_tag(1, 0, TokenType::DoubleQuote),
            Some('$') => self.skip_tag(1, 0, TokenType::Dollar),

            // Newlines are illegal in raw strings.
            Some('\n') => Err(self.error(Syntax::UnexpectedChar('\n'))),

            // Iterate over a sequence of characters, ignoring escape sequences.
            _ => {
                let mut it = self.code.char_indices();
                loop {
                    match it.next() {
                        Some((end, '"' | '$' | '\n')) => {
                            return self.skip_tag(end, 0, TokenType::StringLit);
                        }

                        Some((end, '\\')) => {
                            let c = it.next();
                            if let Some((_, '"' | '\\' | '$')) = c {
                                continue;
                            } else if let Some((_, cc)) = c {
                                let lex = self.skip(end + 1, 0);
                                return Err(lex.error(Syntax::UnexpectedChar(cc)));
                            }
                            continue;
                        }

                        None => {
                            return self.skip_tag(self.code.len(), 0, TokenType::StringLit);
                        }

                        _ => { continue; }
                    }
                }
            }
        }
    }
}

// Allow the lexer to be used as input by some nom combinators that check
// whether sub-parsers consume input or not.
impl<'a> InputLength for Lexer<'a> {
    fn input_len(&self) -> usize {
        self.code.len()
    }
}


/// A lexer with built-in cache, so that the cache cell doesn't have to be
/// passed manually to [`Lexer::next`].
#[derive(Debug, Clone, Copy)]
pub(crate) struct CachedLexer<'a> {
    lexer: Lexer<'a>,
    cache: &'a LexCache<'a>,
}

impl<'a> CachedLexer<'a> {
    /// Construct a new cached lexer. Use [`Lexer::cache`] to make the cache
    /// cell.
    pub fn new(lexer: Lexer<'a>, cache: &'a LexCache<'a>) -> CachedLexer<'a> {
        CachedLexer { lexer, cache }
    }

    /// Return the current buffer position.
    pub fn position(&self) -> Position {
        self.lexer.position()
    }

    /// Construct a new cached lexer with the same cache cell as this one.
    fn cachify(&self, lexer: Lexer<'a>) -> CachedLexer<'a> {
        CachedLexer { lexer, cache: self.cache }
    }

    /// Return an error at the current position.
    pub fn error(&self, reason: Syntax) -> SyntaxError {
        self.lexer.error(reason)
    }

    /// Return the next token in a given context.
    fn next(self, ctx: Ctx) -> CachedLexResult<'a> {
        self.lexer.next(ctx, self.cache).map(
            |(lex, tok)| (self.cachify(lex), tok)
        )
    }

    /// Return the next token in the default context.
    pub fn next_token(self) -> CachedLexResult<'a> {
        self.next(Ctx::Default)
    }

    /// Return the next token in the map context.
    pub fn next_key(self) -> CachedLexResult<'a> {
        self.next(Ctx::Map)
    }

    /// Return the next token in the string context.
    pub fn next_string(self) -> CachedLexResult<'a> {
        self.next(Ctx::String)
    }

    /// Return the next multi-line string token, interrupted at the first line
    /// whose indentation is not greater than `col`.
    pub fn next_multistring(self, col: u32) -> CachedLexResult<'a> {
        self.next(Ctx::MultiString(col))
    }

    /// Skip an arbitrary amount of whitespace (including comments and newlines).
    pub fn skip_whitespace(self) -> CachedLexer<'a> {
        self.lexer.skip_whitespace().with_cache(self.cache)
    }
}

// Allow the cached lexer to be used as input by some nom combinators that check
// whether sub-parsers consume input or not.
impl<'a> InputLength for CachedLexer<'a> {
    fn input_len(&self) -> usize {
        self.lexer.input_len()
    }
}
