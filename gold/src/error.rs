use std::fmt::Debug;

use serde::{Serialize, Deserialize};


#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Location {
    pub offset: usize,
    pub line: u32,
    pub length: usize,
}

impl Location {
    pub fn new(offset: usize, line: u32, length: usize) -> Location {
        Location { offset, line, length }
    }

    pub fn span(l: Location, r: Location) -> Location {
        Location {
            offset: l.offset,
            line: l.line,
            length: r.offset + r.length - l.offset,
        }
    }
}


#[derive(Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Tagged<T> {
    pub location: Location,
    pub contents: T,
}

impl<T> Tagged<T> {
    pub fn new(location: Location, contents: T) -> Tagged<T> {
        Tagged::<T> {
            location,
            contents,
        }
    }

    pub fn loc(&self) -> Location {
        self.location
    }

    pub fn unwrap(self) -> T {
        self.contents
    }

    pub fn map<F, U>(self, f: F) -> Tagged<U> where F: FnOnce(T) -> U {
        Tagged::<U> {
            location: self.location,
            contents: f(self.contents),
        }
    }

    pub fn wraptag<F, U>(self, f: F) -> Tagged<U> where F: FnOnce(Tagged<T>) -> U {
        Tagged::<U> {
            location: self.location,
            contents: f(self),
        }
    }

    pub fn wrap<F, U, V>(self, f: F, loc: V) -> Tagged<U>
    where
        F: FnOnce(Tagged<T>) -> U,
        Location: From<V>
    {
        Tagged::<U> {
            location: Location::from(loc),
            contents: f(self),
        }
    }

    pub fn retag<U>(self, loc: U) -> Tagged<T>
    where
        Location: From<U>,
    {
        Tagged::<T> {
            location: Location::from(loc),
            contents: self.contents,
        }
    }
}

impl<X, Y> Tagged<Result<X,Y>> {
    pub fn transpose(self) -> Result<Tagged<X>,Y> {
        match self.contents {
            Ok(x) => Ok(Tagged { location: self.location, contents: x }),
            Err(y) => Err(y),
        }
    }
}

impl<X> Tagged<Option<X>> {
    pub fn transpose(self) -> Option<Tagged<X>> {
        match self.contents {
            Some(x) => Some(Tagged { location: self.location, contents: x }),
            None => None,
        }
    }
}

impl<T: Debug> Debug for Tagged<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.contents.fmt(f)?;
        f.write_fmt(format_args!(".tag({}, {}, {})", self.location.offset, self.location.line, self.location.length))
    }
}

impl<T> AsRef<T> for Tagged<T> {
    fn as_ref(&self) -> &T {
        &self.contents
    }
}

impl<U,V> From<(U,V)> for Location where Location: From<U> + From<V> {
    fn from((left, right): (U, V)) -> Self {
        let l = Location::from(left);
        let r = Location::from(right);
        Location::span(l, r)
    }
}

impl From<(usize, u32, usize)> for Location {
    fn from((offset, line, length): (usize, u32, usize)) -> Self {
        Location { offset, line, length }
    }
}

impl<T> From<&Tagged<T>> for Location {
    fn from(value: &Tagged<T>) -> Self {
        value.location
    }
}


#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Expected {
    // Characters
    CloseBrace,
    CloseBracket,
    CloseParen,
    Colon,
    Comma,
    DoubleArrow,
    DoubleQuote,
    Equals,
    OpenBrace,
    OpenParen,
    Semicolon,

    // Keywords
    As,
    Else,
    In,
    Then,

    // Grammatical elements
    ArgElement,
    Binding,
    EndOfInput,
    Expression,
    Identifier,
    ImportPath,
    KeywordParam,
    ListBindingElement,
    ListElement,
    MapBindingElement,
    MapElement,
    Operand,
    PosParam,
}


#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SyntaxErrorReason {
    One(Expected),
    Two(Expected, Expected),
    Three(Expected, Expected, Expected),
}

impl From<Expected> for SyntaxErrorReason {
    fn from(v: Expected) -> Self {
        Self::One(v)
    }
}

impl From<(Expected,)> for SyntaxErrorReason {
    fn from((v,): (Expected,)) -> Self {
        Self::One(v)
    }
}

impl From<(Expected,Expected)> for SyntaxErrorReason {
    fn from((u,v): (Expected,Expected)) -> Self {
        Self::Two(u,v)
    }
}

impl From<(Expected,Expected,Expected)> for SyntaxErrorReason {
    fn from((u,v,w): (Expected,Expected,Expected)) -> Self {
        Self::Three(u,v,w)
    }
}


#[derive(Debug, PartialEq)]
pub struct SyntaxError(
    pub Option<Vec<(Location, SyntaxErrorReason)>>
);