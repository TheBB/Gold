use std::fmt::Debug;

use num_bigint::BigInt;

use crate::ast::high::*;
use crate::error::{Action, Error, Reason, Span, Syntax, SyntaxElement, Taggable, Tagged};
use crate::formatting::{
    AlignSpec, FloatFormatType, FormatSpec, FormatType, GroupingSpec, IntegerFormatType, SignSpec, UppercaseSpec,
};
use crate::lexing::{CachedLexer, Ctx, Lexer, Token, TokenType};
use crate::types::{BinOp, EagerOp, Key, UnOp, LogicOp};
use crate::Object;

/// Convert a multiline string from source code to string by removing leading
/// whitespace from each line according to the rules for such strings.
fn multiline(s: &str) -> String {
    let mut lines = s.lines();

    let first = lines.next().unwrap().trim_start();

    let rest: Vec<&str> = lines.filter(|s: &&str| !(*s).trim().is_empty()).collect();
    let indent = rest
        .iter()
        .filter(|s: &&&str| !s.trim().is_empty())
        .map(|s: &&str| {
            (*s).chars()
                .take_while(|c| c.is_whitespace())
                .map(|_| 1)
                .sum()
        })
        .min()
        .unwrap_or(0);

    let mut ret = first.to_string();
    for r in rest {
        if !ret.is_empty() {
            ret += "\n";
        }
        ret += &r.chars().skip(indent).collect::<String>();
    }

    ret
}

/// Temporary expression wrapper used for accurately tracking parenthesized
/// locations.
///
/// For parenthesized expressions, the Gold parser keeps track of both the outer
/// and the inner locations, whereas for non-parenthesized expressions, only the
/// inner location is tracked.
///
/// ```ignore
/// ( some_expression_here )
///   ^----- inner ------^
/// ^------- outer --------^
/// ```
///
/// In this way, when a parenthesized expression becomes a constituent part of
/// a larger expression, the parentheses can be included on both sides, by using
/// the outer span, e.g.:
///
/// ```ignore
/// ( 2 + 3 ) * 5
/// ^-----------^
/// ```
///
/// Instead of the confusing result that would result from using the inner span,
/// incorrectly giving the impression that imbalanced parentheses are allowed:
///
/// ```ignore
/// ( 2 + 3 ) * 5
///   ^---------^
/// ```
///
/// On the other hand, when a parenthesised expression is used in a context where
/// an error originates purely from the inner expression, Gold can disregard the
/// parentheses when reporting the error:
///
/// ```ignore
/// let x = ( some_function(y) ) in x + x
///           ^--------------^
/// ```
#[derive(Clone, Debug)]
enum Paren<T> {
    /// A naked (non-parenthesized) expression.
    Naked(Tagged<T>),

    /// A parenthesized expression with two layers of location tags: outer and inner.
    Parenthesized(Tagged<Tagged<T>>),
}

impl<T> Paren<T> {
    /// Return the inner expression with location tag, disregarding potential
    /// parentheses.
    fn inner(self) -> Tagged<T> {
        match self {
            Self::Naked(x) => x,
            Self::Parenthesized(x) => x.unwrap(),
        }
    }

    /// Return the outermost location span, either parenthesized or not.
    ///
    /// Use this when combining two spans.
    fn outer(&self) -> Span {
        match self {
            Self::Naked(x) => x.span(),
            Self::Parenthesized(x) => x.span(),
        }
    }

    /// Apply `f` to the inner `Tagged<T>` to produce a `U`, preserving the outer `Paren` wrapper.
    ///
    /// Used to lift a plain expression into a wrapper type (e.g. `Expr` → `ListElement::Singleton`)
    /// while keeping the parenthesization information intact.
    fn map_wrap<F, U>(self, f: F) -> Paren<U>
    where
        F: FnOnce(Tagged<T>) -> U,
    {
        match self {
            Self::Naked(x) => Paren::<U>::Naked(x.wrap(f)),
            Self::Parenthesized(x) => Paren::<U>::Parenthesized(x.map(|y| y.wrap(f))),
        }
    }
}

/// Recursive-descent parser that accumulates errors rather than aborting on the first one.
///
/// `CachedLexer` is `Copy`, so saving/restoring `self.lexer` provides unlimited backtracking
/// at essentially zero cost — every speculative parse can be rolled back by saving the lexer
/// before the attempt and restoring it on failure.
struct Parser<'a> {
    lexer: CachedLexer<'a>,
    errors: Vec<Error>,
}

impl<'a> Parser<'a> {
    fn error(&mut self, span: Span, reason: Reason) {
        self.errors.push(Error::new(reason).tag(span, Action::Parse))
    }

    fn loc(&self) -> Span {
        self.lexer.position().with_length(0)
    }

    fn missing_expr(&self) -> Tagged<Expr> {
        return Expr::Missing.tag(self.loc())
    }

    fn missing_paren(&self) -> Paren<Expr> {
        return Paren::Naked(self.missing_expr())
    }

    fn missing_binding(&self) -> Tagged<Binding> {
        return Binding::Missing.tag(self.loc())
    }

    /// Runs `parser`; on failure, records an error and returns `fallback`.
    ///
    /// `fallback` typically inserts a `Missing` sentinel node so the caller can continue
    /// building a structurally complete AST even when a required sub-expression is absent.
    fn require<T>(
        &mut self,
        parser: impl Fn(&mut Parser<'a>) -> Option<T>,
        fallback: impl Fn(&Parser<'a>) -> T,
        reason: impl Fn() -> Reason,
    ) -> T {
        let result = parser(self);
        result.unwrap_or_else(|| {
            self.error(self.loc(), reason());
            fallback(self)
        })
    }

    // ── Token helpers ──────────────────────────────────────────────────────────

    fn try_token(&mut self, kind: TokenType, context: Ctx) -> Option<Tagged<Token<'a>>> {
        match self.lexer.next(context) {
            Ok((lexer, token)) if token.kind == kind => {
                self.lexer = lexer;
                Some(token)
            }
            _ => None
        }
    }

    fn require_token(&mut self, kind: TokenType, context: Ctx) -> Tagged<Option<Token<'a>>> {
        self.require::<Tagged<Option<Token<'a>>>>(
            |parser| parser.try_token(kind, context).map(|t| t.map(Some)),
            |parser| Tagged::new(parser.loc(), None),
            || Reason::from(Syntax::from(kind)),
        )
    }

    /// Try to consume a keyword in normal expression context.
    ///
    /// Uses `next_token()` (not `next_key()`), so the lexer applies expression-context rules.
    fn try_keyword(&mut self, kw: &str) -> Option<Tagged<&'a str>> {
        match self.lexer.next_token() {
            Ok((lexer, token)) if token.kind == TokenType::Name && token.text == kw => {
                self.lexer = lexer;
                Some(token.map(|t| t.text))
            }
            _ => None,
        }
    }

    /// Try to consume a keyword in map-key context.
    ///
    /// Uses `next_key()` so the lexer skips leading newlines/whitespace that separate map entries.
    fn try_map_keyword(&mut self, kw: &str) -> Option<Tagged<&'a str>> {
        match self.lexer.next_key() {
            Ok((lexer, token)) if token.kind == TokenType::Name && token.text == kw => {
                self.lexer = lexer;
                Some(token.map(|t| t.text))
            }
            _ => None,
        }
    }

    fn require_keyword(&mut self, kw: &'a str, element: SyntaxElement) -> Tagged<&'a str> {
        return self.require(
            |parser| parser.try_keyword(kw),
            |parser| kw.tag(parser.loc()),
            || Reason::from(Syntax::from(element)),
        )
    }

    /// Consume an identifier that is not a reserved keyword.
    ///
    /// In expression context, keywords like `for`, `if`, `let` etc. are not valid identifiers.
    /// See `try_map_identifier` for map-key context where keywords *are* valid unquoted keys.
    fn try_identifier(&mut self) -> Option<Tagged<&'a str>> {
        match self.lexer.next_token() {
            Ok((lexer, token)) if token.kind == TokenType::Name && !KEYWORDS.contains(&token.text) => {
                self.lexer = lexer;
                Some(token.map(|t| t.text))
            }
            _ => None
        }
    }

    /// Consume an identifier in map-key context, where keywords are allowed as unquoted keys.
    ///
    /// E.g. `{ for: 1 }` is legal — `for` is a valid string key even though it is a keyword.
    fn try_map_identifier(&mut self) -> Option<Tagged<&'a str>> {
        match self.lexer.next_key() {
            Ok((lexer, token)) if token.kind == TokenType::Name => {
                self.lexer = lexer;
                Some(token.map(|t| t.text))
            }
            _ => None
        }
    }

    // ── Format specifier ──────────────────────────────────────────────────────

    fn try_fmtspec_char(&mut self) -> Option<char> {
        match self.lexer.next_fmtspec() {
            Ok((lexer, token)) if token.kind == TokenType::Char => {
                self.lexer = lexer;
                token.text.chars().next()
            }
            _ => None
        }
    }

    fn try_fmtspec_number(&mut self) -> Option<usize> {
        match self.lexer.next_fmtspec() {
            Ok((lexer, token)) if token.kind == TokenType::Integer => {
                self.lexer = lexer;
                token.text.parse::<usize>().ok()
            }
            _ => None
        }
    }

    /// Attempt to parse a fill character followed by an alignment specifier.
    ///
    /// Requires two-character lookahead: the fill char is only confirmed as fill (not as an
    /// alignment char) once the following character is seen to be `<`, `>`, `^`, or `=`.
    fn try_fmtspec_fill_and_align(&mut self) -> Option<(char, AlignSpec)> {
        let lexer = self.lexer;
        let c1 = self.try_fmtspec_char();
        let c2 = self.try_fmtspec_char();
        match (c1, c2) {
            (Some(c), Some('<')) => Some((c, AlignSpec::left())),
            (Some(c), Some('>')) => Some((c, AlignSpec::right())),
            (Some(c), Some('^')) => Some((c, AlignSpec::center())),
            (Some(c), Some('=')) => Some((c, AlignSpec::AfterSign)),
            _ => { self.lexer = lexer; None }
        }
    }

    fn try_fmtspec_only_align(&mut self) -> Option<AlignSpec> {
        let lexer = self.lexer;
        let c = self.try_fmtspec_char();
        match c {
            Some('<') => Some(AlignSpec::left()),
            Some('>') => Some(AlignSpec::right()),
            Some('^') => Some(AlignSpec::center()),
            Some('=') => Some(AlignSpec::AfterSign),
            _ => { self.lexer = lexer; None }
        }
    }

    fn try_fmtspec_fill_align(&mut self) -> (Option<char>, Option<AlignSpec>) {
        let mut fill: Option<char> = None;
        let mut align: Option<AlignSpec> = None;

        if let Some((f, a)) = self.try_fmtspec_fill_and_align() {
            fill = Some(f);
            align = Some(a);
        } else if let Some(a) = self.try_fmtspec_only_align()  {
            align = Some(a);
        }

        (fill, align)
    }

    fn try_fmtspec_sign(&mut self) -> Option<SignSpec> {
        let lexer = self.lexer;
        let c = self.try_fmtspec_char();
        match c {
            Some('+') => Some(SignSpec::Plus),
            Some('-') => Some(SignSpec::Minus),
            Some(' ') => Some(SignSpec::Space),
            _ => { self.lexer = lexer; None }
        }
    }

    fn require_fmtspec_alternate(&mut self) -> bool {
        let lexer = self.lexer;
        match self.try_fmtspec_char() {
            Some('#') => true,
            _ => { self.lexer = lexer; false }
        }
    }

    fn require_fmtspec_zero(&mut self) -> bool {
        let lexer = self.lexer;
        match self.try_fmtspec_char() {
            Some('0') => true,
            _ => { self.lexer = lexer; false }
        }
    }

    fn try_fmtspec_grouping(&mut self) -> Option<GroupingSpec> {
        let lexer = self.lexer;
        match self.try_fmtspec_char() {
            Some(',') => Some(GroupingSpec::Comma),
            Some('_') => Some(GroupingSpec::Underscore),
            _ => { self.lexer = lexer; None }
        }
    }

    fn try_fmtspec_precision(&mut self) -> Option<usize> {
        let lexer = self.lexer;
        let c = self.try_fmtspec_char();
        let n = self.try_fmtspec_number();
        match (c, n) {
            (Some('.'), Some(n)) => Some(n),
            (Some('.'), _) => Some(0),
            _ => { self.lexer = lexer; None }
        }
    }

    fn try_fmtspec_type(&mut self) -> Option<FormatType> {
        let lexer = self.lexer;
        let c = self.try_fmtspec_char();
        match c {
            Some('s') => Some(FormatType::String),
            Some('b') => Some(FormatType::Integer(IntegerFormatType::Binary)),
            Some('c') => Some(FormatType::Integer(IntegerFormatType::Character)),
            Some('d') => Some(FormatType::Integer(IntegerFormatType::Decimal)),
            Some('o') => Some(FormatType::Integer(IntegerFormatType::Octal)),
            Some('x') => Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
            Some('X') => Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Upper))),
            Some('e') => Some(FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Lower))),
            Some('E') => Some(FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Upper))),
            Some('f') => Some(FormatType::Float(FloatFormatType::Fixed)),
            Some('g') => Some(FormatType::Float(FloatFormatType::General)),
            Some('%') => Some(FormatType::Float(FloatFormatType::Percentage)),
            _ => { self.lexer = lexer; None }
        }
    }

    fn require_fmtspec(&mut self) -> FormatSpec {
        let (fill, align) = self.try_fmtspec_fill_align();
        let sign = self.try_fmtspec_sign();
        let alternate = self.require_fmtspec_alternate();
        let zero = self.require_fmtspec_zero();
        let width = self.try_fmtspec_number();
        let grouping = self.try_fmtspec_grouping();
        let precision = self.try_fmtspec_precision();
        let fmt_type = self.try_fmtspec_type();

        // Mirroring Python's format-spec mini-language: `0` without an explicit fill/align means
        // "pad with zeros after the sign", i.e. fill='0' + align=AfterSign.  An explicit fill/align
        // always wins over the zero flag.
        let has_explicit_fa = fill.is_some() || align.is_some();
        let fill = fill.unwrap_or(if zero { '0' } else { ' ' });
        let align = if has_explicit_fa { align } else if zero { Some(AlignSpec::AfterSign) } else { None };

        FormatSpec { fill, align, sign, alternate, width, grouping, precision, fmt_type }
    }

    // ── Strings ───────────────────────────────────────────────────────────────

    fn try_raw_string_content(&mut self) -> Option<String> {
        let mut chars = self.try_token(TokenType::StringLit, Ctx::String)?.text.char_indices();
        let mut out = "".to_string();
        loop {
            match chars.next() {
                Some((_, '\\')) => match chars.next() {
                    Some((_, '\\')) => {
                        out += "\\";
                    }
                    Some((_, '"')) => {
                        out += "\"";
                    }
                    Some((_, '$')) => {
                        out += "$";
                    }
                    Some((_, _)) => {
                        // TODO: Calculate accurate error
                        continue;
                    }
                    None => {
                        // TODO: Calculate accurate error
                        break;
                    }
                },
                Some((_, c)) => out.push(c),
                None => {
                    break;
                }
            }
        }

        Some(out)
    }

    fn try_string_interp(&mut self) -> Option<StringElement> {
        if self.try_token(TokenType::Dollar, Ctx::String).is_none() {
            return None;
        }

        self.require_token(TokenType::OpenBrace, Ctx::Default);
        let expr = self.require_expr();

        let mut fmtspec: Option<FormatSpec> = None;
        if self.try_token(TokenType::Colon, Ctx::Default).is_some() {
            fmtspec = Some(self.require_fmtspec());
            self.require_token(TokenType::CloseBrace, Ctx::FmtSpec);
        } else {
            self.require_token(TokenType::CloseBrace, Ctx::Default);
        }

        Some(StringElement::Interpolate(expr.inner(), fmtspec))
    }

    fn try_string_part(&mut self) -> Option<Tagged<Vec<StringElement>>> {
        match self.try_token(TokenType::DoubleQuote, Ctx::Default) {
            None => None,
            Some(open_q) => {
                let mut elements: Vec<StringElement> = Vec::new();
                loop {
                    if let Some(element) = self.try_string_interp() {
                        elements.push(element);
                        continue;
                    }
                    if let Some(element) = self.try_raw_string_content() {
                        elements.push(StringElement::raw(element));
                        continue;
                    }
                    break;
                }
                let close_q = self.require_token(TokenType::DoubleQuote, Ctx::Default);
                Some(elements.tag(open_q.span()..close_q.span()))
            }
        }
    }

    /// Parse a string expression, merging adjacent quoted segments into a single node.
    ///
    /// Gold allows adjacent string literals to be written side by side and they are
    /// joined at parse time: `"hello " "world"` becomes the single string `"hello world"`.
    fn try_string(&mut self) -> Option<Tagged<Expr>> {
        match self.try_string_part() {
            None => None,
            Some(first) => {
                let mut span = first.span();
                let mut elements = first.unwrap();

                loop {
                    match self.try_string_part() {
                        None => { break }
                        Some(more) => {
                            span = Span::from(span..more.span());
                            elements.extend(more.unwrap().into_iter());
                        }
                    }
                }

                Some(Expr::string(elements).tag(span))
            }
        }
    }

    // ── Separated-list kernel ─────────────────────────────────────────────────

    /// Core separated-list parser with error recovery.
    ///
    /// `try_item` returns `(item, skip_next_sep)`.  When `skip_next_sep` is `true` the item
    /// consumed its own logical separator (e.g. a multistring value terminated by dedent), so
    /// the loop does not look for a separator before the next item.
    ///
    /// Error recovery: if a separator is expected but missing, the parser checks whether what
    /// follows is the closing delimiter (end the list) or another item (emit a missing-separator
    /// error and keep going).  If an item is expected but missing, the list is closed immediately.
    fn seplist_inner<T, S>(
        &mut self,
        try_item: impl Fn(&mut Parser<'a>) -> Option<(Tagged<T>, bool)>,
        try_sep: impl Fn(&mut Parser<'a>) -> Option<Tagged<S>>,
        try_close: impl Fn(&mut Parser<'a>) -> Option<Tagged<Token<'a>>>,
        err_missing_item: Reason,
        err_missing_sep: Reason,
        close_tok_type: TokenType,
    ) -> (Vec<Tagged<T>>, Tagged<Option<Token<'a>>>) {
        let mut items: Vec<Tagged<T>> = vec![];
        let mut close: Option<Tagged<Token<'a>>>;
        let mut need_sep: bool = false;

        loop {
            if need_sep {
                if try_sep(self).is_some() {
                    need_sep = false;
                    continue;
                }
                close = try_close(self);
                if close.is_some() { break; }

                let loc = self.loc();
                let lexer = self.lexer;
                match try_item(self) {
                    None => { self.lexer = lexer; break; }
                    Some((item, skip_next_sep)) => {
                        self.error(loc, err_missing_sep.clone());
                        items.push(item);
                        need_sep = !skip_next_sep;
                    }
                }
            } else {
                close = try_close(self);
                if close.is_some() { break; }

                match try_item(self) {
                    None => {
                        self.error(self.loc(), err_missing_item);
                        close = try_close(self);
                        if close.is_none() {
                            close = Some(Token { kind: close_tok_type, text: "" }.tag(self.loc()));
                        }
                        break;
                    }
                    Some((item, skip_next_sep)) => {
                        items.push(item);
                        need_sep = !skip_next_sep;
                    }
                }
            }
        }

        (items, close.map(|t| t.map(Some)).unwrap_or_else(|| self.require_token(close_tok_type, Ctx::Default)))
    }

    fn try_seplist<T, S>(
        &mut self,
        try_open: impl Fn(&mut Parser<'a>) -> Option<Tagged<Token<'a>>>,
        try_item: impl Fn(&mut Parser<'a>) -> Option<(Tagged<T>, bool)>,
        try_sep: impl Fn(&mut Parser<'a>) -> Option<Tagged<S>>,
        try_close: impl Fn(&mut Parser<'a>) -> Option<Tagged<Token<'a>>>,
        err_missing_item: Reason,
        err_missing_sep: Reason,
        close_tok_type: TokenType,
    ) -> Option<(Tagged<Token<'a>>, Vec<Tagged<T>>, Tagged<Option<Token<'a>>>)> {
        match try_open(self) {
            None => None,
            Some(open) => {
                let (items, close) = self.seplist_inner(
                    try_item,
                    try_sep,
                    try_close,
                    err_missing_item,
                    err_missing_sep,
                    close_tok_type,
                );
                Some((open, items, close))
            }
        }
    }

    // ── Numbers / atomics ─────────────────────────────────────────────────────

    fn try_number(&mut self) -> Option<Tagged<Expr>> {
        self.try_token(TokenType::Float, Ctx::Default).map(|tok| {
            tok.text.replace("_", "")
                .parse::<f64>()
                .map(|x| Expr::Literal(Object::from(x)).tag(tok.span()))
        }).and_then(|x| x.ok()).or_else(|| {
            self.try_token(TokenType::Integer, Ctx::Default).map(|tok| {
                let text = tok.text.replace("_", "");
                text.parse::<i64>()
                    .map(Object::from)
                    .or_else(|_| text.parse::<BigInt>().map(Object::from))
                    .map(|obj| Expr::Literal(obj).tag(tok.span()))
            }).and_then(|x| x.ok())
        })
    }

    fn try_atomic(&mut self) -> Option<Tagged<Expr>> {
        if let Some(tok) = self.try_keyword("null") {
            return Some(Expr::Literal(Object::null()).tag(tok.span()))
        }
        if let Some(tok) = self.try_keyword("true") {
            return Some(Expr::Literal(Object::from(true)).tag(tok.span()))
        }
        if let Some(tok) = self.try_keyword("false") {
            return Some(Expr::Literal(Object::from(false)).tag(tok.span()))
        }
        self.try_number().or_else(|| self.try_string())
    }

    // ── Lists ──────────────────────────────────────────────────────────────────

    fn try_list_element(&mut self) -> Option<Paren<ListElement>> {
        if let Some(start) = self.try_token(TokenType::Ellipsis, Ctx::Default) {
            let expr = self.require_expr();
            let span = Span::from(start.span()..expr.outer());
            return Some(Paren::Naked(
                ListElement::Splat(expr.inner()).tag(span)
            ))
        }

        if let Some(start) = self.try_keyword("for") {
            let binding = self.require_binding();
            self.require_keyword("in", SyntaxElement::In);
            let iterable = self.require_expr();
            self.require_token(TokenType::Colon, Ctx::Default);
            let element = self.require_list_element();
            let span = Span::from(start.span()..element.outer());
            return Some(Paren::Naked(
                ListElement::Loop {
                    binding,
                    iterable: iterable.inner(),
                    element: Box::new(element.inner()),
                }.tag(span)
            ))
        }

        if let Some(start) = self.try_keyword("when") {
            let condition = self.require_expr();
            self.require_token(TokenType::Colon, Ctx::Default);
            let element = self.require_list_element();
            let span = Span::from(start.span()..element.outer());
            return Some(Paren::Naked(
                ListElement::Cond {
                    condition: condition.inner(),
                    element: Box::new(element.inner()),
                }.tag(span)
            ))
        }

        if let Some(expr) = self.try_expr() {
            return Some(expr.map_wrap(|e| ListElement::Singleton(e)))
        }

        None
    }

    fn require_list_element(&mut self) -> Paren<ListElement> {
        self.require(
            |parser| parser.try_list_element(),
            |parser| Paren::Naked(ListElement::Singleton(parser.missing_expr()).tag(parser.loc())),
            || Reason::from(Syntax::from(SyntaxElement::ListElement)),
        )
    }

    fn try_list(&mut self) -> Option<Tagged<Expr>> {
        self.try_seplist(
            |parser| parser.try_token(TokenType::OpenBracket, Ctx::Default),
            |parser| parser.try_list_element().map(|x| (x.inner(), false)),
            |parser| parser.try_token(TokenType::Comma, Ctx::Default),
            |parser| parser.try_token(TokenType::CloseBracket, Ctx::Default),
            Reason::from(Syntax::from((TokenType::CloseBracket, SyntaxElement::ListElement))),
            Reason::from(Syntax::from((TokenType::Comma, TokenType::CloseBracket))),
            TokenType::CloseBracket,
        ).map(|(open, list, close)| Expr::List(list).tag(open.span()..close.span()))
    }

    // ── Map ───────────────────────────────────────────────────────────────────

    fn try_map_key(&mut self) -> Option<Tagged<Expr>> {
        if let Some(s) = self.try_string() {
            return Some(s);
        }
        if let Some(s) = self.try_map_identifier() {
            return Some(s.map(|x| Expr::Literal(Object::from(x))));
        }
        None
    }

    fn try_map_element(&mut self) -> Option<(Tagged<MapElement>, bool)> {
        // Map entries may be on separate lines; advance past any leading whitespace/newlines
        // before attempting to lex the next token in map-key context.
        self.lexer = self.lexer.skip_whitespace();

        if let Some(start) = self.try_token(TokenType::Ellipsis, Ctx::Map) {
            let expr = self.require_expr();
            let span = Span::from(start.span()..expr.outer());
            return Some((MapElement::Splat(expr.inner()).tag(span), false));
        }

        if let Some(start) = self.try_map_keyword("for") {
            let binding = self.require_binding();
            self.require_keyword("in", SyntaxElement::In);
            let iterable = self.require_expr().inner();
            self.require_token(TokenType::Colon, Ctx::Default);
            let (element, skip) = self.require_map_element();
            let span = Span::from(start.span()..element.span());
            return Some((
                MapElement::Loop {
                    binding,
                    iterable,
                    element: Box::new(element),
                }.tag(span),
                skip,
            ));
        }

        if let Some(start) = self.try_map_keyword("when") {
            let condition = self.require_expr().inner();
            self.require_token(TokenType::Colon, Ctx::Default);
            let (element, skip) = self.require_map_element();
            let span = Span::from(start.span()..element.span());
            return Some((
                MapElement::Cond {
                    condition,
                    element: Box::new(element),
                }.tag(span),
                skip,
            ));
        }

        if let Some(start) = self.try_token(TokenType::Dollar, Ctx::Map) {
            let key = self.require_expr().inner();
            self.require_token(TokenType::Colon, Ctx::Default);
            let value = self.require_expr();
            let span = Span::from(start.span()..value.outer());
            return Some((
                MapElement::Singleton {
                    key,
                    value: value.inner(),
                }.tag(span),
                false,
            ));
        }

        if let Some(key) = self.try_map_key() {
            if let Some(_) = self.try_token(TokenType::DoubleColon, Ctx::Map) {
                let value = match self.lexer.next_multistring(key.span().column()) {
                    Ok((lexer, token)) => {
                        self.lexer = lexer;
                        Expr::Literal(Object::from(multiline(token.text))).tag(token.span())
                    }
                    Err(_) => {
                        self.error(self.loc(), Reason::from(Syntax::from(TokenType::MultiString)));
                        self.missing_expr()
                    }
                };
                let span = Span::from(key.span()..value.span());
                return Some((MapElement::Singleton { key, value }.tag(span), true));
            }

            self.require_token(TokenType::Colon, Ctx::Map);
            let value = self.require_expr();
            let span = Span::from(key.span()..value.outer());
            return Some((MapElement::Singleton { key, value: value.inner() }.tag(span), false));
        }

        None
    }

    fn require_map_element(&mut self) -> (Tagged<MapElement>, bool) {
        self.require(
            |parser| parser.try_map_element(),
            |parser| (
                MapElement::Singleton {
                    key: parser.missing_expr(),
                    value: parser.missing_expr(),
                }.tag(parser.loc()),
                false,
            ),
            || Reason::from(Syntax::from(SyntaxElement::MapElement)),
        )
    }

    fn try_map(&mut self) -> Option<Tagged<Expr>> {
        self.try_seplist(
            |parser| parser.try_token(TokenType::OpenBrace, Ctx::Default),
            |parser| parser.try_map_element(),
            |parser| parser.try_token(TokenType::Comma, Ctx::Default),
            |parser| parser.try_token(TokenType::CloseBrace, Ctx::Default),
            Reason::from(Syntax::from((TokenType::CloseBrace, SyntaxElement::MapElement))),
            Reason::from(Syntax::from((TokenType::Comma, TokenType::CloseBrace))),
            TokenType::CloseBrace,
        ).map(|(open, list, close)| Expr::Map(list).tag(open.span()..close.span()))
    }

    // ── Postfix expressions ───────────────────────────────────────────────────

    fn try_postfixable(&mut self) -> Option<Paren<Expr>> {
        if let Some(start) = self.try_token(TokenType::OpenParen, Ctx::Default) {
            let expr = self.require_expr();
            let close = self.require_token(TokenType::CloseParen, Ctx::Default);
            let span = Span::from(start.span()..close.span());
            return Some(Paren::Parenthesized(expr.inner().tag(span)));
        }

        if let Some(atom) = self.try_atomic() {
            return Some(Paren::Naked(atom));
        }

        if let Some(ident) = self.try_identifier() {
            let span = ident.span();
            return Some(Paren::Naked(Expr::Identifier(Key::new(*ident).tag(span)).tag(span)))
        }

        if let Some(list) = self.try_list() {
            return Some(Paren::Naked(list));
        }

        if let Some(map) = self.try_map() {
            return Some(Paren::Naked(map));
        }

        None
    }

    fn try_postfix_transform(&mut self) -> Option<Tagged<Transform>> {
        if let Some(dot) = self.try_token(TokenType::Dot, Ctx::Default) {
            let key_expr = match self.try_identifier() {
                Some(name) => name.map(|s| Expr::Literal(Object::from(s))),
                None => {
                    self.error(self.loc(), Reason::from(Syntax::from(SyntaxElement::Identifier)));
                    self.missing_expr()
                }
            };
            let span = Span::from(dot.span()..key_expr.span());
            return Some(Transform::index(key_expr, dot.span()).tag(span));
        }

        if let Some(open_b) = self.try_token(TokenType::OpenBracket, Ctx::Default) {
            let subscript = self.require_expr().inner();
            let close_b = self.require_token(TokenType::CloseBracket, Ctx::Default);
            let op_span = Span::from(open_b.span()..close_b.span());
            return Some(Transform::index(subscript, op_span).tag(op_span));
        }

        if let Some(open_p) = self.try_token(TokenType::OpenParen, Ctx::Default) {
            let (args, close_p) = self.require_arg_list();
            let call_span = Span::from(open_p.span()..close_p.span());
            return Some(Transform::FunCall(args.tag(call_span)).tag(call_span));
        }

        None
    }

    fn try_postfixed(&mut self) -> Option<Paren<Expr>> {
        let mut pexpr = self.try_postfixable()?;
        while let Some(transform) = self.try_postfix_transform() {
            let span = Span::from(pexpr.outer()..transform.span());
            pexpr = Paren::Naked(
                Expr::Transformed {
                    operand: Box::new(pexpr.inner()),
                    transform: transform.unwrap(),
                }.tag(span)
            );
        }
        Some(pexpr)
    }

    fn require_arg_list(&mut self) -> (Vec<Tagged<ArgElement>>, Tagged<Option<Token<'_>>>) {
        return self.seplist_inner(
            |parser| parser.try_function_arg().map(|x| (x, false)),
            |parser| parser.try_token(TokenType::Comma, Ctx::Default),
            |parser| parser.try_token(TokenType::CloseParen, Ctx::Default),
            Reason::from(Syntax::from((TokenType::CloseParen, SyntaxElement::ArgElement))),
            Reason::from(Syntax::from((TokenType::Comma, TokenType::CloseParen))),
            TokenType::CloseParen,
        )
    }

    fn try_function_arg(&mut self) -> Option<Tagged<ArgElement>> {
        if let Some(start) = self.try_token(TokenType::Ellipsis, Ctx::Default) {
            let expr = self.require_expr();
            let span = Span::from(start.span()..expr.outer());
            return Some(ArgElement::Splat(expr.inner()).tag(span));
        }

        let lexer = self.lexer;
        if let Some(key) = self.try_identifier() {
            if let Some(_) = self.try_token(TokenType::Colon, Ctx::Default) {
                let expr = self.require_expr();
                let span = Span::from(key.span()..expr.outer());
                return Some(ArgElement::Keyword(key.map(Key::new), expr.inner()).tag(span));
            } else {
                self.lexer = lexer;
            }
        }

        if let Some(expr) = self.try_expr() {
            let span = expr.outer();
            return Some(ArgElement::Singleton(expr.inner()).tag(span));
        }

        None
    }

    // ── Operator precedence ───────────────────────────────────────────────────
    //
    // Tightest to loosest:
    //   postfixed (calls/indexing) → power (right-assoc) → prefix unary →
    //   product (* / //) → sum (+ -) → inequality (< <= > >=) → equality (== !=) →
    //   contains (has) → conjunction (and) → disjunction (or)

    fn try_power(&mut self) -> Option<Paren<Expr>> {
        let base = self.try_postfixed()?;
        let Some(caret) = self.try_token(TokenType::Caret, Ctx::Default) else { return Some(base) };
        let rhs = self.try_prefixed().unwrap_or_else(|| {
            self.error(self.loc(), Reason::from(Syntax::from(SyntaxElement::Operand)));
            self.missing_paren()
        });

        let span = Span::from(base.outer()..rhs.outer());
        return Some(Paren::Naked(
            Expr::Transformed {
                operand: Box::new(base.inner()),
                transform: Transform::BinOp(
                    BinOp::Eager(EagerOp::Power).tag(caret.span()),
                    Box::new(rhs.inner()),
                ),
            }.tag(span)
        ))
    }

    fn try_prefixed(&mut self) -> Option<Paren<Expr>> {
        let mut ops: Vec<Tagged<Option<UnOp>>> = vec![];
        loop {
            if let Some(tok) = self.try_token(TokenType::Plus, Ctx::Default) {
                ops.push(None.tag(tok.span()));
            } else if let Some(tok) = self.try_token(TokenType::Minus, Ctx::Default) {
                ops.push(Some(UnOp::ArithmeticalNegate).tag(tok.span()));
            } else if let Some(tok) = self.try_keyword("not") {
                ops.push(Some(UnOp::LogicalNegate).tag(tok.span()));
            } else {
                break;
            }
        }

        let mut operand = self.try_power().or_else(|| {
            if !ops.is_empty() {
                self.error(self.loc(), Reason::from(Syntax::from(SyntaxElement::Operand)));
                Some(self.missing_paren())
            } else {
                None
            }
        })?;

        for op in ops.into_iter().rev() {
            let span = Span::from(op.span()..operand.outer());
            operand = Paren::Naked(
                Expr::Transformed {
                    operand: Box::new(operand.inner()),
                    transform: Transform::UnOp(op),
                }.tag(span)
            )
        }

        Some(operand)
    }

    /// Left-associative binary-operator parser: `a op b op c` folds to `(a op b) op c`.
    fn try_lbinop(
        &mut self,
        try_sub: impl Fn(&mut Parser<'a>) -> Option<Paren<Expr>>,
        try_op: impl Fn(&mut Parser<'a>) -> Option<Tagged<BinOp>>,
    ) -> Option<Paren<Expr>> {
        let mut lhs = try_sub(self)?;

        loop {
            let Some(op) = try_op(self) else { break };
            let rhs = try_sub(self).unwrap_or_else(|| {
                self.error(self.loc(), Reason::from(Syntax::from(SyntaxElement::Operand)));
                self.missing_paren()
            });

            let span = Span::from(lhs.outer()..rhs.outer());
            lhs = Paren::Naked(
                Expr::Transformed {
                    operand: Box::new(lhs.inner()),
                    transform: Transform::BinOp(op, Box::new(rhs.inner())),
                }.tag(span)
            )
        }

        Some(lhs)
    }

    fn try_product(&mut self) -> Option<Paren<Expr>> {
        self.try_lbinop(
            |parser| parser.try_prefixed(),
            |parser| {
                parser.try_token(TokenType::Asterisk, Ctx::Default)
                .map(|t| BinOp::Eager(EagerOp::Multiply).tag(t.span()))
                .or_else(|| {
                    parser.try_token(TokenType::DoubleSlash, Ctx::Default)
                    .map(|t| BinOp::Eager(EagerOp::IntegerDivide).tag(t.span()))
                })
                .or_else(|| {
                    parser.try_token(TokenType::Slash, Ctx::Default)
                    .map(|t| BinOp::Eager(EagerOp::Divide).tag(t.span()))
                })
            }
        )
    }

    fn try_sum(&mut self) -> Option<Paren<Expr>> {
        self.try_lbinop(
            |parser| parser.try_product(),
            |parser| {
                parser.try_token(TokenType::Plus, Ctx::Default)
                .map(|t| BinOp::Eager(EagerOp::Add).tag(t.span()))
                .or_else(|| {
                    parser.try_token(TokenType::Minus, Ctx::Default)
                    .map(|t| BinOp::Eager(EagerOp::Subtract).tag(t.span()))
                })
            }
        )
    }

    fn try_inequality(&mut self) -> Option<Paren<Expr>> {
        self.try_lbinop(
            |parser| parser.try_sum(),
            |parser| {
                parser.try_token(TokenType::LessEq, Ctx::Default)
                .map(|t| BinOp::Eager(EagerOp::LessEqual).tag(t.span()))
                .or_else(|| {
                    parser.try_token(TokenType::Less, Ctx::Default)
                    .map(|t| BinOp::Eager(EagerOp::Less).tag(t.span()))
                })
                .or_else(|| {
                    parser.try_token(TokenType::GreaterEq, Ctx::Default)
                    .map(|t| BinOp::Eager(EagerOp::GreaterEqual).tag(t.span()))
                })
                .or_else(|| {
                    parser.try_token(TokenType::Greater, Ctx::Default)
                    .map(|t| BinOp::Eager(EagerOp::Greater).tag(t.span()))
                })
            }
        )
    }

    fn try_equality(&mut self) -> Option<Paren<Expr>> {
        self.try_lbinop(
            |parser| parser.try_inequality(),
            |parser| {
                parser.try_token(TokenType::DoubleEq, Ctx::Default)
                .map(|t| BinOp::Eager(EagerOp::Equal).tag(t.span()))
                .or_else(|| {
                    parser.try_token(TokenType::ExclamEq, Ctx::Default)
                    .map(|t| BinOp::Eager(EagerOp::NotEqual).tag(t.span()))
                })
            }
        )
    }

    fn try_contains(&mut self) -> Option<Paren<Expr>> {
        self.try_lbinop(
            |parser| parser.try_equality(),
            |parser| {
                parser.try_keyword("has")
                .map(|t| BinOp::Eager(EagerOp::Contains).tag(t.span()))
            }
        )
    }

    fn try_conjunction(&mut self) -> Option<Paren<Expr>> {
        self.try_lbinop(
            |parser| parser.try_contains(),
            |parser| {
                parser.try_keyword("and")
                .map(|t| BinOp::Logic(LogicOp::And).tag(t.span()))
            }
        )
    }

    fn try_disjunction(&mut self) -> Option<Paren<Expr>> {
        self.try_lbinop(
            |parser| parser.try_conjunction(),
            |parser| {
                parser.try_keyword("or")
                .map(|t| BinOp::Logic(LogicOp::Or).tag(t.span()))
            }
        )
    }

    // ── Composite expressions ─────────────────────────────────────────────────

    fn try_let(&mut self) -> Option<Paren<Expr>> {
        let start = self.try_keyword("let")?.span();

        let mut bindings: Vec<(Tagged<Binding>, Tagged<Expr>)> = vec![];
        loop {
            let binding = self.require_binding();
            self.require_token(TokenType::Eq, Ctx::Default);
            let expr = self.require_expr();
            bindings.push((binding, expr.inner()));
            if self.try_keyword("let").is_none() { break }
        }

        self.require_keyword("in", SyntaxElement::In);
        let body = self.require_expr();

        let span = Span::from(start..body.outer());
        return Some(Paren::Naked(
            Expr::Let { bindings, expression: Box::new(body.inner()) }.tag(span)
        ));
    }

    fn try_branch(&mut self) -> Option<Paren<Expr>> {
        let start = self.try_keyword("if")?.span();
        let cond = self.require_expr();
        self.require_keyword("then", SyntaxElement::Then);
        let true_br = self.require_expr();
        self.require_keyword("else", SyntaxElement::Else);
        let false_br = self.require_expr();

        let span = Span::from(start..false_br.outer());
        return Some(Paren::Naked(
            Expr::Branch {
                condition: Box::new(cond.inner()),
                true_branch: Box::new(true_br.inner()),
                false_branch: Box::new(false_br.inner()),
            }.tag(span)
        ))
    }

    fn try_function(&mut self) -> Option<Paren<Expr>> {
        self.try_fn_new_style()
            .or_else(|| self.try_fn_old_kw_style())
            .or_else(|| self.try_fn_old_pos_style())
    }

    // ── Binding helpers used by function parsers ───────────────────────────────

    fn parse_list_binding_terminated(
        &mut self,
        try_close: impl Fn(&mut Parser<'a>) -> Option<Tagged<Token<'a>>>,
        close_tok_type: TokenType,
        start_span: Span,
    ) -> (Tagged<ListBinding>, Tagged<Option<Token<'a>>>) {
        let (elements, close) = self.seplist_inner(
            |parser| parser.try_list_binding_element().map(|x| (x, false)),
            |parser| parser.try_token(TokenType::Comma, Ctx::Default),
            try_close,
            Reason::from(Syntax::from((SyntaxElement::PosParam, TokenType::CloseParen))),
            Reason::from(Syntax::from((TokenType::Comma, TokenType::CloseParen))),
            close_tok_type,
        );

        return (ListBinding::new(elements).tag(Span::from(start_span..close.span())), close)
    }

    fn parse_map_binding_terminated(
        &mut self,
        try_close: impl Fn(&mut Parser<'a>) -> Option<Tagged<Token<'a>>>,
        close_tok_type: TokenType,
        start_span: Span,
    ) -> (Tagged<MapBinding>, Tagged<Option<Token<'a>>>) {
        let (elements, close) = self.seplist_inner(
            |parser| parser.try_map_binding_element().map(|x| (x, false)),
            |parser| parser.try_token(TokenType::Comma, Ctx::Default),
            try_close,
            Reason::from(Syntax::from((SyntaxElement::KeywordParam, TokenType::CloseParen))),
            Reason::from(Syntax::from((TokenType::Comma, TokenType::CloseParen))),
            close_tok_type,
        );

        return (MapBinding::new(elements).tag(Span::from(start_span..close.span())), close)
    }

    // ── Function syntax variants ───────────────────────────────────────────────
    //
    // Gold supports three function syntaxes:
    //   new-style:      fn (pos1, pos2; kw1, kw2) body    (parentheses; `;` separates pos/kw)
    //                   fn {kw1, kw2} body                (braces = keyword-only)
    //   old-style kw:   {| kw1, kw2 |} body
    //   old-style pos:  |pos1, pos2| body
    //                   |pos1; kw1| body                  (`;` separates pos/kw)
    //
    // All three are still accepted by the parser for backwards compatibility.

    fn try_fn_new_style(&mut self) -> Option<Paren<Expr>> {
        let start = self.try_keyword("fn")?.span();

        let (pos, kw, expr) = if let Some(open) = self.try_token(TokenType::OpenParen, Ctx::Default) {
            // The positional-param list is closed by either `)` (no keywords) or `;` (keywords follow).
            let (pos, term) = self.parse_list_binding_terminated(
                |parser| {
                    parser.try_token(TokenType::CloseParen, Ctx::Default)
                    .or_else(|| parser.try_token(TokenType::SemiColon, Ctx::Default))
                },
                TokenType::CloseParen,
                open.span(),
            );

            let (kw, missing_close) = if term.is_some_and(|t| t.kind == TokenType::SemiColon) {
                let (kw, close) = self.parse_map_binding_terminated(
                    |parser| parser.try_token(TokenType::CloseParen, Ctx::Default),
                    TokenType::CloseParen,
                    term.span(),
                );

                (Some(kw), close.is_none())
            } else {
                (None, term.is_none())
            };

            let expr = if missing_close { self.missing_paren() } else { self.require_expr() };
            (pos, kw, expr)
        } else if let Some(open) = self.try_token(TokenType::OpenBrace, Ctx::Default) {
            let (kw, close) = self.parse_map_binding_terminated(
                |parser| parser.try_token(TokenType::CloseBrace, Ctx::Default),
                TokenType::CloseBrace,
                open.span(),
            );

            let expr = if close.is_none() { self.missing_paren() } else { self.require_expr() };

            (
                ListBinding::new(vec![]).tag(open.span()),
                Some(kw),
                expr,
            )
        } else {
            self.error(self.loc(), Reason::from(Syntax::from((TokenType::OpenParen, TokenType::OpenBrace))));
            (
                ListBinding::new(vec![]).tag(start),
                None,
                self.missing_paren(),
            )
        };

        let span = Span::from(start..expr.outer());
        Some(Paren::Naked(
            Expr::Function {
                positional: pos,
                keywords: kw,
                expression: Box::new(expr.inner()),
            }.tag(span)
        ))
    }

    fn try_fn_old_kw_style(&mut self) -> Option<Paren<Expr>> {
        let start = self.try_token(TokenType::OpenBracePipe, Ctx::Default)?.span();
        let (kw, close) = self.parse_map_binding_terminated(
            |parser| parser.try_token(TokenType::CloseBracePipe, Ctx::Default),
            TokenType::CloseBracePipe,
            start,
        );

        let expr = if close.is_none() { self.missing_paren() } else { self.require_expr() };
        let span = Span::from(start..expr.outer());
        Some(Paren::Naked(
            Expr::Function {
                positional: ListBinding::new(vec![]).tag(start.with_length(1)),
                keywords: Some(kw),
                expression: Box::new(expr.inner()),
            }.tag(span)
        ))
    }

    fn try_fn_old_pos_style(&mut self) -> Option<Paren<Expr>> {
        let start = self.try_token(TokenType::Pipe, Ctx::Default)?.span();
        let (pos, close) = self.parse_list_binding_terminated(
            |parser| {
                parser.try_token(TokenType::Pipe, Ctx::Default)
                    .or_else(|| parser.try_token(TokenType::SemiColon, Ctx::Default))
            },
            TokenType::Pipe,
            start,
        );

        let (kw, close) = if close.is_some_and(|t| t.kind == TokenType::SemiColon) {
            let (kw, term) = self.parse_map_binding_terminated(
                |parser| parser.try_token(TokenType::Pipe, Ctx::Default),
                TokenType::Pipe,
                close.span(),
            );

            (Some(kw), term)
        } else {
            (None, close)
        };

        let expr = if close.is_none() { self.missing_paren() } else { self.require_expr() };
        let span = Span::from(start..expr.outer());
        Some(Paren::Naked(
            Expr::Function {
                positional: pos,
                keywords: kw,
                expression: Box::new(expr.inner()),
            }.tag(span)
        ))
    }

    // ── Top-level expression ───────────────────────────────────────────────────

    fn try_expr(&mut self) -> Option<Paren<Expr>> {
        self.try_let()
            .or_else(|| self.try_branch())
            .or_else(|| self.try_function())
            .or_else(|| self.try_disjunction())
    }

    fn require_expr(&mut self) -> Paren<Expr> {
        self.require(
            |parser| parser.try_expr(),
            |parser| parser.missing_paren(),
            || Reason::from(Syntax::from(SyntaxElement::Expression)),
        )
    }

    // ── Bindings ──────────────────────────────────────────────────────────────

    fn try_list_binding_element(&mut self) -> Option<Tagged<ListBindingElement>> {
        if let Some(ellipsis) = self.try_token(TokenType::Ellipsis, Ctx::Default) {
            return Some(
                match self.try_identifier() {
                    Some(name) => ListBindingElement::SlurpTo(name.map(Key::new)).tag(ellipsis.span()..name.span()),
                    None => ListBindingElement::Slurp.tag(ellipsis.span()),
                }
            );
        }

        let binding = self.try_binding()?;
        if self.try_token(TokenType::Eq, Ctx::Default).is_some() {
            let default = self.require_expr();
            let span = Span::from(binding.span()..default.outer());
            Some(
                ListBindingElement::Binding {
                    binding,
                    default: Some(default.inner()),
                }.tag(span)
            )
        } else {
            let span = binding.span();
            Some(binding.map(|binding| ListBindingElement::Binding { binding: binding.tag(span), default: None}))
        }
    }

    fn try_map_binding_element(&mut self) -> Option<Tagged<MapBindingElement>> {
        if let Some(ellipsis) = self.try_token(TokenType::Ellipsis, Ctx::Default) {
            // Map slurp always requires a name to bind the rest-object to, unlike list slurp
            // which may appear as a bare `...` to discard remaining elements.
            return Some(
                match self.try_identifier() {
                    Some(name) => MapBindingElement::SlurpTo(name.map(Key::new)).tag(ellipsis.span()..name.span()),
                    None => {
                        self.error(self.loc(), Reason::from(Syntax::from(SyntaxElement::Identifier)));
                        let name = Key::new("").tag(self.loc());
                        MapBindingElement::SlurpTo(name).tag(ellipsis.span())
                    }
                }
            );
        }

        let name = self.try_identifier()?.map(Key::new);
        let sub_binding = self
            .try_keyword("as")
            .map(|_| self.require_binding())
            .unwrap_or_else(|| Binding::Identifier(name).tag(name.span()));
        let default = self
            .try_token(TokenType::Eq, Ctx::Default)
            .map(|_| self.require_expr());

        let end = default.as_ref().map(|x| x.outer()).unwrap_or_else(|| sub_binding.span());

        Some(
            MapBindingElement::Binding {
                key: name,
                binding: sub_binding,
                default: default.map(|x| x.inner()),
            }.tag(name.span()..end)
        )
    }

    fn try_binding(&mut self) -> Option<Tagged<Binding>> {
        if let Some(name) = self.try_identifier() {
            let span = name.span();
            return Some(name.map(|x| Binding::Identifier(Key::new(x).tag(span))));
        }

        if let Some(tok) = self.try_token(TokenType::OpenBracket, Ctx::Default) {
            let (binding, _) = self.parse_list_binding_terminated(
                |parser| parser.try_token(TokenType::CloseBracket, Ctx::Default),
                TokenType::CloseBracket,
                tok.span(),
            );
            let span = binding.span();
            return Some(Binding::List(binding).tag(span));
        }

        if let Some(tok) = self.try_token(TokenType::OpenBrace, Ctx::Default) {
            let (binding, _) = self.parse_map_binding_terminated(
                |parser| parser.try_token(TokenType::CloseBrace, Ctx::Default),
                TokenType::CloseBrace,
                tok.span(),
            );
            let span = binding.span();
            return Some(Binding::Map(binding).tag(span));
        }

        None
    }

    fn require_binding(&mut self) -> Tagged<Binding> {
        self.require(
            |parser| parser.try_binding(),
            |parser| parser.missing_binding(),
            || Reason::from(Syntax::from(SyntaxElement::Binding)),
        )
    }

    // ── Top-level statements ───────────────────────────────────────────────────

    fn try_import(&mut self) -> Option<TopLevel> {
        self.try_keyword("import")?;
        let open = self.require_token(TokenType::DoubleQuote, Ctx::Default).span();
        let path = self.try_raw_string_content().unwrap_or_else(|| "".into());
        let close = self.require_token(TokenType::DoubleQuote, Ctx::Default).span();
        let path = path.tag(Span::from(open..close));

        self.require_keyword("as", SyntaxElement::As);
        let binding = self.require_binding();

        Some(TopLevel::Import(path, binding))
    }

    fn parse(&mut self) -> File {
        let mut statements: Vec<TopLevel> = vec![];
        while let Some(stmt) = self.try_import() {
            statements.push(stmt);
        }

        let expr = self.require_expr();

        if !self.lexer.at_eof() {
            let pos = self.lexer.skip_whitespace().position();
            self.error(pos.with_length(0), Reason::from(Syntax::from(SyntaxElement::EndOfInput)));
        }

        File { statements, expression: expr.inner() }
    }
}

/// The result of parsing a Gold source file.
///
/// Always contains a structurally complete AST (`tree`), possibly with
/// `Missing` sentinels at positions where sub-expressions were absent.
/// Errors are accumulated in `errors`; an empty list means the parse succeeded.
pub struct ParseResult {
    /// The parsed AST. Always structurally complete; positions where sub-expressions were
    /// absent are filled with `Missing` sentinel nodes.
    pub tree: File,
    /// All parse errors encountered. Empty on a clean parse.
    pub errors: Vec<Error>,
}

impl ParseResult {
    /// Returns `true` when the parse completed without any errors.
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Parse a Gold source string into a [`ParseResult`].
pub fn parse(input: &str) -> ParseResult {
    let cache = Lexer::cache();
    let lexer = Lexer::new(input).with_cache(&cache);
    let mut parser = Parser { lexer, errors: vec![] };
    let tree = parser.parse();
    ParseResult { tree, errors: parser.errors }
}

/// List of keywords that must be avoided by the [`identifier`] parser.
static KEYWORDS: [&'static str; 17] = [
    "for", "when", "if", "then", "else", "let", "in", "has", "true", "false", "null", "and", "or",
    "not", "as", "import", "fn",
];
