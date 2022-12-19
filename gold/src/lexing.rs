use std::iter::Iterator;
use regex::Regex;

use crate::error::{Location, Tagged};
use crate::traits::Taggable;


#[derive(Debug, PartialEq)]
pub(crate) enum Token<'a> {
    Dollar,
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

    Unexpected(char),
}


#[derive(Clone, Copy, PartialEq)]
enum Delim {
    Brace,
    Bracket,
    DoubleQuote,
    Dollar,
    File,
    Paren,

    Error,
}


#[derive(Clone, Copy, PartialEq)]
enum Ctx {
    Default,
    String,
    IntName,

    Error,
}


pub(crate) struct Lexer<'a> {
    code: &'a str,
    offset: usize,
    line: u32,
    context_stack: Vec<(Ctx, Delim)>,
}


lazy_static! {
    static ref WHITESPACE: Regex = Regex::new(r"^[^\S\n]+").unwrap();
    static ref NAME: Regex = Regex::new("^[[:alpha:]_][^\\s'\"{}()\\[\\]/+*\\-;:,.=]*").unwrap();
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
            context_stack: vec![(Ctx::Default, Delim::File)],
        }
    }

    fn context(&self) -> (Ctx, Delim) {
        self.context_stack.last().copied().unwrap()
    }

    fn push(&mut self, context: (Ctx, Delim)) {
        self.context_stack.push(context);
    }

    fn pop(&mut self) -> Option<(Ctx, Delim)> {
        self.context_stack.pop()
    }

    fn peek(&mut self) -> Option<char> {
        self.code.chars().next()
    }

    fn double_peek(&mut self) -> (Option<char>, Option<char>) {
        let mut chars = self.code.chars();
        let a = chars.next();
        let b = chars.next();
        (a, b)
    }

    fn skip(&mut self, offset: usize, delta_line: u32) {
        self.code = &self.code[offset..];
        self.offset += offset;
        self.line += delta_line;
    }

    fn skip_tag<F, T>(&mut self, offset: usize, mapper: F) -> Option<Tagged<T>>
    where
        F: FnOnce(&'a str) -> T
    {
        let ret = self.code[..offset].tag(Location {
            offset: self.offset,
            line: self.line,
            length: offset,
        }).map(mapper);

        self.skip(offset, 0);
        Some(ret)
    }

    fn traverse(&mut self, regex: &Regex) -> Option<Tagged<&'a str>> {
        regex.find(self.code).map(|m| {
            let ret = m.as_str().tag(Location {
                offset: self.offset + m.start(),
                line: self.line,
                length: m.end() - m.start(),
            });

            self.skip(m.end(), 0);

            ret
        })
    }

    fn skip_whitespace(&mut self) {
        loop {
            self.traverse(&WHITESPACE).and_then(|s| { println!("{:?}", s.as_ref()); Some(1) });

            match self.peek() {
                Some('\n') => {
                    self.skip(1, 1);
                    continue;
                },
                Some('#') => {
                    let end = self.code.find('\n').unwrap_or(self.code.len() - 1);
                    self.skip(end + 1, 1);
                },
                _ => {
                    break;
                },
            }
        }
    }

    fn next_number(&mut self) -> Option<Tagged<Token<'a>>> {
        if let Some(t) = self.traverse(&FLOAT_A) {
            return Some(t.map(Token::Float));
        }

        if let Some(t) = self.traverse(&FLOAT_B) {
            return Some(t.map(Token::Float));
        }

        if let Some(t) = self.traverse(&FLOAT_C) {
            return Some(t.map(Token::Float));
        }

        if let Some(t) = self.traverse(&DIGITS) {
            return Some(t.map(Token::Integer));
        }

        None
    }

    fn next_name(&mut self) -> Option<Tagged<Token<'a>>> {
        self.traverse(&NAME).map(|t| Token::Name(t.as_ref()).tag(t.loc()))
    }

    fn next_string(&mut self) -> Option<Tagged<Token<'a>>> {
        match self.peek() {
            None => { return None; },

            _ => {
                let mut it = self.code.char_indices();
                loop {
                    match it.next() {
                        Some((end, '"')) => {
                            return self.skip_tag(end, Token::StringLit);
                        }

                        Some((end, '$')) => {
                            return self.skip_tag(end, Token::StringLit);
                        }

                        Some((end, '\n')) => {
                            self.push((Ctx::Error, Delim::Error));
                            self.skip(end, 0);
                            return self.skip_tag(1, |_| Token::Unexpected('\n'));
                        }

                        Some((_, '\\')) => {
                            if let Some((end, '\n')) = it.next() {
                                self.push((Ctx::Error, Delim::Error));
                                self.skip(end, 0);
                                return self.skip_tag(1, |_| Token::Unexpected('\n'));
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


impl<'a> Iterator for Lexer<'a> {
    type Item = Tagged<Token<'a>>;

    fn next(&mut self) -> Option<Self::Item> {

        match (self.context(), self.peek()) {

            // Error state: immediate bail
            ((Ctx::Error, _), _) => {
                return None;
            }

            // String state with terminating quote
            ((Ctx::String, Delim::DoubleQuote), Some('"')) => {
                self.pop();
                return self.skip_tag(1, |_| Token::DoubleQuote);
            }

            // String state with interpolation
            ((Ctx::String, Delim::DoubleQuote), Some('$')) => {
                self.push((Ctx::IntName, Delim::Dollar));
                return self.skip_tag(1, |_| Token::Dollar);
            }

            // String state with other character
            ((Ctx::String, Delim::DoubleQuote), _) => {
                return self.next_string();
            }

            // Interpolation state with curly brace
            ((Ctx::IntName, Delim::Dollar), Some('{')) => {
                self.pop();
                self.push((Ctx::Default, Delim::Brace));
                return self.skip_tag(1, |_| Token::OpenBrace);
            }

            // Interpolation state with any other character
            ((Ctx::IntName, Delim::Dollar), _) => {
                self.pop();
                return self.next_name();
            }

            _ => {}
        }

        self.skip_whitespace();

        match (self.context(), self.double_peek()) {

            // Closing scopes
            ((_, Delim::Brace), (Some('}'), _)) => {
                self.pop();
                return self.skip_tag(1, |_| Token::CloseBrace);
            }

            ((_, Delim::Bracket), (Some(']'), _)) => {
                self.pop();
                return self.skip_tag(1, |_| Token::CloseBracket);
            }

            ((_, Delim::Paren), (Some(')'), _)) => {
                self.pop();
                return self.skip_tag(1, |_| Token::CloseParen);
            }

            // Opening scopes
            ((Ctx::Default, _), (Some('"'), _)) => {
                self.push((Ctx::String, Delim::DoubleQuote));
                return self.skip_tag(1, |_| Token::DoubleQuote);
            }

            ((Ctx::Default, _), (Some('['), _)) => {
                self.push((Ctx::Default, Delim::Bracket));
                return self.skip_tag(1, |_| Token::OpenBracket);
            }

            ((Ctx::Default, _), (Some('{'), _)) => {
                self.push((Ctx::Default, Delim::Brace));
                return self.skip_tag(1, |_| Token::OpenBrace);
            }

            ((Ctx::Default, _), (Some('('), _)) => {
                self.push((Ctx::Default, Delim::Paren));
                return self.skip_tag(1, |_| Token::OpenParen);
            }

            // Other
            ((Ctx::Default, _), (Some(','), _)) => {
                return self.skip_tag(1, |_| Token::Comma);
            }

            ((Ctx::Default, _), (Some(':'), _)) => {
                return self.skip_tag(1, |_| Token::Colon);
            }

            ((Ctx::Default, _), (Some('.'), Some('.')))
            if self.code.chars().nth(2) == Some('.') => {
                return self.skip_tag(3, |_| Token::Ellipsis);
            }

            ((Ctx::Default, _), (Some(x), _))
            if x.is_ascii_digit() => {
                return self.next_number();
            }

            ((Ctx::Default, _), (Some('.'), Some(x)))
            if x.is_ascii_digit() => {
                return self.next_number();
            }

            ((Ctx::Default, _), _) => {
                return self.next_name();
            }

            _ => {}
        }

        None
    }
}
