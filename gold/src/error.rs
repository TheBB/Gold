use std::{fmt::Debug, path::PathBuf};

use serde::{Serialize, Deserialize};

use crate::ast::{BinOp};
use crate::object::{Key, Type};


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

    pub fn tag_error(&self, action: Action) -> impl Fn(Error) -> Error {
        let loc = self.loc();
        move |err: Error| err.tag(loc, action)
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

impl<T> From<&Tagged<T>> for Location {
    fn from(value: &Tagged<T>) -> Self {
        value.location
    }
}


#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SyntaxElement {
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
    ExpectedOne(SyntaxElement),
    ExpectedTwo(SyntaxElement, SyntaxElement),
    ExpectedThree(SyntaxElement, SyntaxElement, SyntaxElement),
}

impl From<SyntaxElement> for SyntaxErrorReason {
    fn from(v: SyntaxElement) -> Self {
        Self::ExpectedOne(v)
    }
}

impl From<(SyntaxElement,)> for SyntaxErrorReason {
    fn from((v,): (SyntaxElement,)) -> Self {
        Self::ExpectedOne(v)
    }
}

impl From<(SyntaxElement,SyntaxElement)> for SyntaxErrorReason {
    fn from((u,v): (SyntaxElement,SyntaxElement)) -> Self {
        Self::ExpectedTwo(u,v)
    }
}

impl From<(SyntaxElement,SyntaxElement,SyntaxElement)> for SyntaxErrorReason {
    fn from((u,v,w): (SyntaxElement,SyntaxElement,SyntaxElement)) -> Self {
        Self::ExpectedThree(u,v,w)
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum InternalErrorReason {
    SetInFrozenNamespace,
}


#[derive(Debug, Clone, PartialEq)]
pub enum BindingType {
    Identifier,
    List,
    Map,
}


#[derive(Debug, Clone, PartialEq)]
pub enum UnpackErrorReason {
    ListTooShort,
    ListTooLong,
    KeyMissing(Key),
    TypeMismatch(BindingType, Type)
}


#[derive(Debug, Clone, PartialEq)]
pub enum TypeMismatchErrorReason {
    Iterate(Type),
    SplatList(Type),
    SplatMap(Type),
    SplatArg(Type),
    MapKey(Type),
    BinOp(Type, Type, BinOp)
}


#[derive(Debug, Clone, PartialEq)]
pub enum FileSystemErrorReason {
    NoParent(PathBuf),
    Read(PathBuf),
}


#[derive(Debug, PartialEq)]
pub enum ErrorReason {
    None,
    Syntax(SyntaxErrorReason),
    Unbound(Key),
    Unpack(UnpackErrorReason),
    Internal(InternalErrorReason),
    TypeMismatch(TypeMismatchErrorReason),
    FileSystem(FileSystemErrorReason),
    UnknownImport(String),
}

impl From<SyntaxErrorReason> for ErrorReason {
    fn from(value: SyntaxErrorReason) -> Self {
        Self::Syntax(value)
    }
}

impl From<InternalErrorReason> for ErrorReason {
    fn from(value: InternalErrorReason) -> Self {
        Self::Internal(value)
    }
}

impl From<UnpackErrorReason> for ErrorReason {
    fn from(value: UnpackErrorReason) -> Self {
        Self::Unpack(value)
    }
}

impl From<TypeMismatchErrorReason> for ErrorReason {
    fn from(value: TypeMismatchErrorReason) -> Self {
        Self::TypeMismatch(value)
    }
}

impl From<FileSystemErrorReason> for ErrorReason {
    fn from(value: FileSystemErrorReason) -> Self {
        Self::FileSystem(value)
    }
}


#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Action {
    Parse,
    LookupName,
    Bind,
    Slurp,
    Splat,
    Iterate,
    Assign,
    Import,
    Evaluate,
}


#[derive(Debug, PartialEq, Default)]
pub struct Error {
    pub locations: Option<Vec<(Location, Action)>>,
    pub reason: Option<ErrorReason>,
}

impl Error {
    pub fn tag<T>(mut self, loc: T, action: Action) -> Self where Location: From<T> {
        match &mut self.locations {
            None => { self.locations = Some(vec![(Location::from(loc), action)]); },
            Some(vec) => { vec.push((Location::from(loc), action)); },
        }
        self
    }

    pub fn with_reason<T>(reason: T) -> Self where ErrorReason: From<T> {
        Self {
            locations: None,
            reason: Some(ErrorReason::from(reason)),
        }
    }

    pub fn unbound(key: Key) -> Self {
        Self::with_reason(ErrorReason::Unbound(key))
    }
}
