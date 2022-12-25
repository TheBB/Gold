use std::iter::Iterator;
use regex::Regex;

use crate::error::{Location, Tagged, SyntaxError, Syntax, SyntaxElement};
use crate::traits::Taggable;


type LexResult<'a, T> = Result<(Lexer<'a>, T), SyntaxError>;


#[derive(Debug, PartialEq)]
pub(crate) enum Token<'a> {
    Dollar,
    DoubleComma,
    DoubleQuote,
    OpenBrace,
    OpenBracket,
    OpenParen,
    CloseBrace,
    CloseBracket,
    CloseParen,
    Colon,
    Comma,
    Ellipsis,

    Name(&'a str),
    Float(&'a str),
    Integer(&'a str),
    StringLit(&'a str),
    MultiString(&'a str),

    Unexpected(char),
}


#[derive(Clone, Copy)]
pub(crate) struct Lexer<'a> {
    code: &'a str,
    offset: usize,
    line: u32,
    col: u32,
}


lazy_static! {
    static ref WHITESPACE: Regex = Regex::new(r"^[^\S\n]*").unwrap();
    static ref NAME: Regex = Regex::new("^[[:alpha:]_][^\\s'\"{}()\\[\\]/+*\\-;:,.=#]*").unwrap();
    static ref KEY: Regex = Regex::new("^[^\\s'\"{}()\\[\\]:]+").unwrap();
    static ref FLOAT_A: Regex = Regex::new(r"^[[:digit:]][[:digit:]_]*\.[[:digit:]_]*(?:(?:e|E)(?:\+|-)?[[:digit:]][[:digit:]_]*)?").unwrap();
    static ref FLOAT_B: Regex = Regex::new(r"^\.[[:digit:]][[:digit:]_]*(?:(?:e|E)[[:digit:]][[:digit:]_]*)?").unwrap();
    static ref FLOAT_C: Regex = Regex::new(r"^[[:digit:]][[:digit:]_]*(?:e|E)(?:\+|-)?[[:digit:]][[:digit:]_]*").unwrap();
    static ref DIGITS: Regex = Regex::new("^[[:digit:]][[:digit:]_]*").unwrap();
}


impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Lexer<'a> {
        Lexer {
            code,
            offset: 0,
            line: 1,
            col: 0,
        }
    }

    fn loc(&self) -> Location {
        Location {
            offset: self.offset,
            line: self.line,
            column: self.col as u32,
            length: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.code.chars().next()
    }

    fn satisfies_at(&self, i: usize, f: impl FnOnce(char) -> bool) -> bool {
        self.code.chars().nth(i).is_some_and(f)
    }

    fn skip(self, offset: usize, delta_line: u32) -> Self {
        Lexer {
            code: &self.code[offset..],
            offset: self.offset + offset,
            line: self.line + delta_line,
            col: if delta_line > 0 { 0 } else { self.col + offset as u32 }
        }
    }

    fn skip_tag<T>(self, offset: usize, mapper: impl FnOnce(&'a str) -> T) -> LexResult<'a, Tagged<T>>
    {
        let ret = self.code[..offset].tag(Location {
            offset: self.offset,
            column: self.col,
            line: self.line,
            length: offset,
        }).map(mapper);

        Ok((self.skip(offset, 0), ret))
    }

    // fn skip_tag_col<T>(self, offset: usize, mapper: impl FnOnce(&'a str) -> T) -> LexResult<'a, (usize, Tagged<T>)>
    // {
    //     let col = self.col;
    //     let (lex, tok) = self.skip_tag(offset, mapper).unwrap();
    //     Ok((lex, (col, tok)))
    // }

    fn traverse(self, regex: &'a Regex, element: SyntaxElement) -> LexResult<Tagged<&'a str>> {
        regex.find(self.code).map(|m| {
            let ret = m.as_str().tag(Location {
                offset: self.offset + m.start(),
                line: self.line,
                column: self.col,
                length: m.end() - m.start(),
            });

            (self.skip(m.end(), 0), ret)
        }).ok_or_else(
            || SyntaxError(self.loc(), Some(Syntax::from(element)))
        )
    }

    fn skip_whitespace(mut self) -> Self {
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

    fn skip_indent(self) -> Self {
        // The WHITESPACE regex cannot fail to match, so unwrapping is safe
        self.traverse(&WHITESPACE, SyntaxElement::Whitespace).unwrap().0
    }

    fn next_number(self) -> LexResult<'a, Tagged<Token<'a>>> {
        self.traverse(&FLOAT_A, SyntaxElement::Number)
        .or_else(|_| self.traverse(&FLOAT_B, SyntaxElement::Number))
        .or_else(|_| self.traverse(&FLOAT_C, SyntaxElement::Number))
        .map(|(lex, tok)| (lex, tok.map(Token::Float)))
        .or_else(|_| self.traverse(&DIGITS, SyntaxElement::Number).map(|(lex, tok)| (lex, tok.map(Token::Integer))))
    }

    fn next_name(self, regex: &'a Regex) -> LexResult<'a, Tagged<Token<'a>>> {
        let col = self.col;
        self.traverse(regex, SyntaxElement::Identifier).map(
            |(lex, tok)| (lex, tok.map(Token::Name))
        )
    }

    pub fn next_token(mut self) -> LexResult<'a, Tagged<Token<'a>>> {
        self = self.skip_whitespace();

        match self.peek() {
            Some('a'..='z') | Some('A'..='Z') | Some('_') => self.next_name(&NAME),

            Some(x) if x.is_ascii_digit() => self.next_number(),
            Some('.') if self.satisfies_at(1, |x| x.is_ascii_digit()) => self.next_number(),

            Some('.') if self.satisfies_at(1, |x| x == '.') && self.satisfies_at(2, |x| x == '.') => self.skip_tag(3, |_| Token::Ellipsis),

            Some(':') if self.satisfies_at(1, |x| x == ':') => self.skip_tag(2, |_| Token::DoubleComma),
            Some(':') => self.skip_tag(1, |_| Token::Colon),

            Some('"') => self.skip_tag(1, |_| Token::DoubleQuote),
            Some('{') => self.skip_tag(1, |_| Token::OpenBrace),
            Some('}') => self.skip_tag(1, |_| Token::CloseBrace),
            Some('[') => self.skip_tag(1, |_| Token::OpenBracket),
            Some(']') => self.skip_tag(1, |_| Token::CloseBracket),
            Some('(') => self.skip_tag(1, |_| Token::OpenParen),
            Some(')') => self.skip_tag(1, |_| Token::CloseParen),
            Some(',') => self.skip_tag(1, |_| Token::Comma),

            Some(c) => Err(SyntaxError(self.loc(), Some(Syntax::UnexpectedChar(c)))),
            None => Err(SyntaxError(self.loc(), Some(Syntax::UnexpectedEof))),
        }
    }

    pub fn next_key(mut self) -> LexResult<'a, Tagged<Token<'a>>> {
        self = self.skip_whitespace();

        match self.peek() {
            Some('}') => self.skip_tag(1, |_| Token::CloseBrace),
            Some('$') => self.skip_tag(1, |_| Token::Dollar),
            Some('"') => self.skip_tag(1, |_| Token::DoubleQuote),
            Some('.') if self.satisfies_at(1, |x| x == '.') && self.satisfies_at(2, |x| x == '.') => self.skip_tag(3, |_| Token::Ellipsis),
            Some(_) => self.next_name(&KEY),
            None => Err(SyntaxError(self.loc(), Some(Syntax::UnexpectedEof))),
        }
    }

    pub fn next_multistring(mut self, col: u32) -> LexResult<'a, Tagged<Token<'a>>> {
        let orig = self;

        let end = self.code.find('\n').unwrap_or(self.code.len() - 1);
        self = self.skip(end + 1, 1);

        loop {
            let skipped = self.skip_indent();
            if skipped.col <= col {
                break;
            }

            self = skipped;

            let end = self.code.find('\n').unwrap_or(self.code.len() - 1);
            self = self.skip(end + 1, 1);
        }

        let tok = Token::MultiString(&orig.code[..(self.offset - orig.offset)]).tag(Location {
            offset: orig.offset,
            line: orig.line,
            column: orig.col,
            length: self.offset - orig.offset,
        });

        Ok((self, tok))
    }

    pub fn next_string(self) -> LexResult<'a, Tagged<Token<'a>>> {
        match self.peek() {
            None => Err(SyntaxError(self.loc(), Some(Syntax::UnexpectedEof))),

            Some('"') => self.skip_tag(1, |_| Token::DoubleQuote),
            Some('$') => self.skip_tag(1, |_| Token::Dollar),
            Some('\n') => self.skip_tag(1, |_| Token::Unexpected('\n')),

            _ => {
                let mut it = self.code.char_indices();
                loop {
                    match it.next() {
                        Some((end, '"' | '$' | '\n')) => {
                            return self.skip_tag(end, Token::StringLit);
                        }

                        Some((end, '\\')) => {
                            let c = it.next();
                            if let Some((_, '"' | '\\' | '$')) = c {
                                continue;
                            } else if let Some((_, cc)) = c {
                                return self.skip(end + 1, 0).skip_tag(1, |_| Token::Unexpected(cc))
                            }
                            continue;
                        }

                        None => {
                            return self.skip_tag(self.code.len(), Token::StringLit);
                        }

                        _ => { continue; }
                    }
                }
            }
        }
    }
}
