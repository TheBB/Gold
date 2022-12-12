use std::cmp::min;
use std::fmt::{Debug, Display, Write};
use std::path::PathBuf;

use serde::{Serialize, Deserialize};

use crate::ast::{BinOp, UnOp};
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
    CloseCurlyPipe,
    CloseParen,
    Colon,
    Comma,
    DoubleArrow,
    DoubleQuote,
    Equals,
    OpenBrace,
    OpenParen,
    Pipe,
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
    MapValue,
    Operand,
    PosParam,
}


#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Syntax {
    ExpectedOne(SyntaxElement),
    ExpectedTwo(SyntaxElement, SyntaxElement),
    ExpectedThree(SyntaxElement, SyntaxElement, SyntaxElement),
    MultiSlurp,
}

impl From<SyntaxElement> for Syntax {
    fn from(v: SyntaxElement) -> Self {
        Self::ExpectedOne(v)
    }
}

impl From<(SyntaxElement,)> for Syntax {
    fn from((v,): (SyntaxElement,)) -> Self {
        Self::ExpectedOne(v)
    }
}

impl From<(SyntaxElement,SyntaxElement)> for Syntax {
    fn from((u,v): (SyntaxElement,SyntaxElement)) -> Self {
        Self::ExpectedTwo(u,v)
    }
}

impl From<(SyntaxElement,SyntaxElement,SyntaxElement)> for Syntax {
    fn from((u,v,w): (SyntaxElement,SyntaxElement,SyntaxElement)) -> Self {
        Self::ExpectedThree(u,v,w)
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum Internal {
    SetInFrozenNamespace,
}


#[derive(Debug, Clone, PartialEq)]
pub enum BindingType {
    Identifier,
    List,
    Map,
}


#[derive(Debug, Clone, PartialEq)]
pub enum Unpack {
    ListTooShort,
    ListTooLong,
    KeyMissing(Key),
    TypeMismatch(BindingType, Type)
}


#[derive(Debug, Clone, PartialEq)]
pub enum TypeMismatch {
    Iterate(Type),
    SplatList(Type),
    SplatMap(Type),
    SplatArg(Type),
    MapKey(Type),
    Interpolate(Type),
    BinOp(Type, Type, BinOp),
    UnOp(Type, UnOp),
    Call(Type),
    Json(Type),

    ExpectedArg(usize, Vec<Type>, Type),
    ArgCount(usize, usize, usize),
}


#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    OutOfRange,
    TooLarge,
    TooLong,
    Convert(Type),
}


#[derive(Debug, Clone, PartialEq)]
pub enum FileSystem {
    NoParent(PathBuf),
    Read(PathBuf),
}


#[derive(Debug, PartialEq)]
pub enum Reason {
    None,
    Syntax(Syntax),
    Unbound(Key),
    Unassigned(Key),
    Unpack(Unpack),
    Internal(Internal),
    External(String),
    TypeMismatch(TypeMismatch),
    Value(Value),
    FileSystem(FileSystem),
    UnknownImport(String),
}

impl From<Syntax> for Reason {
    fn from(value: Syntax) -> Self {
        Self::Syntax(value)
    }
}

impl From<Internal> for Reason {
    fn from(value: Internal) -> Self {
        Self::Internal(value)
    }
}

impl From<Unpack> for Reason {
    fn from(value: Unpack) -> Self {
        Self::Unpack(value)
    }
}

impl From<TypeMismatch> for Reason {
    fn from(value: TypeMismatch) -> Self {
        Self::TypeMismatch(value)
    }
}

impl From<FileSystem> for Reason {
    fn from(value: FileSystem) -> Self {
        Self::FileSystem(value)
    }
}

impl From<Value> for Reason {
    fn from(value: Value) -> Self {
        Self::Value(value)
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
    Format,
}


#[derive(Debug, PartialEq, Default)]
pub struct Error {
    pub locations: Option<Vec<(Location, Action)>>,
    pub reason: Option<Reason>,
    pub rendered: Option<String>,
}

impl Error {
    pub fn tag<T>(mut self, loc: T, action: Action) -> Self where Location: From<T> {
        match &mut self.locations {
            None => { self.locations = Some(vec![(Location::from(loc), action)]); },
            Some(vec) => { vec.push((Location::from(loc), action)); },
        }
        self
    }

    pub fn new<T>(reason: T) -> Self where Reason: From<T> {
        Self {
            locations: None,
            reason: Some(Reason::from(reason)),
            rendered: None,
        }
    }

    pub fn unbound(key: Key) -> Self {
        Self::new(Reason::Unbound(key))
    }

    pub fn unrender(self) -> Self {
        Self {
            locations: self.locations,
            reason: self.reason,
            rendered: None,
        }
    }

    pub fn render(self, code: &str) -> Self {
        let rendered = format!("{}", ErrorRenderer(&self, code));
        Self {
            locations: self.locations,
            reason: self.reason,
            rendered: Some(rendered),
        }
    }
}


struct ErrorRenderer<'a>(&'a Error, &'a str);

impl Display for SyntaxElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::ArgElement => "function argument",
            Self::As => "'as'",
            Self::Binding => "binding pattern",
            Self::CloseBrace => "'}'",
            Self::CloseBracket => "']'",
            Self::CloseCurlyPipe => "|}",
            Self::CloseParen => "')'",
            Self::Colon => "':'",
            Self::Comma => "','",
            Self::DoubleArrow => "'=>'",
            Self::DoubleQuote => "'\"'",
            Self::Else => "'else'",
            Self::EndOfInput => "end of input",
            Self::Equals => "'='",
            Self::Expression => "expression",
            Self::Identifier => "identifier",
            Self::ImportPath => "import path",
            Self::In => "'in'",
            Self::KeywordParam => "keyword parameter",
            Self::ListBindingElement => "list binding pattern",
            Self::ListElement => "list element",
            Self::MapBindingElement => "map binding pattern",
            Self::MapElement => "map element",
            Self::MapValue => "map value",
            Self::OpenBrace => "'{'",
            Self::OpenParen => "'('",
            Self::Operand => "operand",
            Self::Pipe => "|",
            Self::PosParam => "positional parameter",
            Self::Semicolon => "';'",
            Self::Then => "'then'",
        };

        f.write_str(s)
    }
}

impl Display for BindingType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identifier => f.write_str("identifier"),
            Self::List => f.write_str("list"),
            Self::Map => f.write_str("map"),
        }
    }
}

impl Display for Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::None => f.write_str("unknown reason - this should not happen, please file a bug report"),

            Self::Syntax(Syntax::ExpectedOne(x)) => f.write_fmt(format_args!("expected {}", x)),
            Self::Syntax(Syntax::ExpectedTwo(x, y)) => f.write_fmt(format_args!("expected {} or {}", x, y)),
            Self::Syntax(Syntax::ExpectedThree(x, y, z)) => f.write_fmt(format_args!("expected {}, {} or {}", x, y, z)),
            Self::Syntax(Syntax::MultiSlurp) => f.write_str("only one slurp allowed in this context"),

            Self::Unbound(key) => f.write_fmt(format_args!("unbound name '{}'", key)),

            Self::Unassigned(key) => f.write_fmt(format_args!("unbound key '{}'", key)),

            Self::Unpack(Unpack::KeyMissing(key)) => f.write_fmt(format_args!("unbound key '{}'", key)),
            Self::Unpack(Unpack::ListTooLong) => f.write_str("list too long"),
            Self::Unpack(Unpack::ListTooShort) => f.write_str("list too short"),
            Self::Unpack(Unpack::TypeMismatch(x, y)) => f.write_fmt(format_args!("expected {}, found {}", x, y)),

            Self::Internal(Internal::SetInFrozenNamespace) => f.write_str("internal error 001 - this should not happen, please file a bug report"),

            Self::External(reason) => f.write_fmt(format_args!("external error: {}", reason)),

            Self::TypeMismatch(TypeMismatch::ArgCount(min, max, actual)) => {
                if min == max && *max == 1 {
                    f.write_fmt(format_args!("expected 1 argument, got {}", actual))
                } else if min == max {
                    f.write_fmt(format_args!("expected {} arguments, got {}", min, actual))
                } else {
                    f.write_fmt(format_args!("expected {} to {} arguments, got {}", min, max, actual))
                }
            },
            Self::TypeMismatch(TypeMismatch::BinOp(l, r, op)) => f.write_fmt(format_args!("unsuitable types for '{}': {} and {}", op, l, r)),
            Self::TypeMismatch(TypeMismatch::Call(x)) => f.write_fmt(format_args!("unsuitable type for function call: {}", x)),
            Self::TypeMismatch(TypeMismatch::ExpectedArg(i, types, actual)) => {
                f.write_fmt(format_args!("unsuitable type for parameter {} - expected ", i + 1))?;
                match types[..] {
                    [] => {},
                    [t] => f.write_fmt(format_args!("{}", t))?,
                    _ => {
                        let s = types[0..types.len() - 1].iter().map(|t| format!("{}", t)).collect::<Vec<String>>().join(", ");
                        f.write_fmt(format_args!("{} or {}", s, types.last().unwrap()))?
                    }
                }
                f.write_fmt(format_args!(", got {}", actual))
            },
            Self::TypeMismatch(TypeMismatch::Interpolate(x)) => f.write_fmt(format_args!("unsuitable type for string interpolation: {}", x)),
            Self::TypeMismatch(TypeMismatch::Iterate(x)) => f.write_fmt(format_args!("non-iterable type: {}", x)),
            Self::TypeMismatch(TypeMismatch::Json(x)) => f.write_fmt(format_args!("unsuitable type for JSON-like conversion: {}", x)),
            Self::TypeMismatch(TypeMismatch::MapKey(x)) => f.write_fmt(format_args!("unsuitable type for map key: {}", x)),
            Self::TypeMismatch(TypeMismatch::SplatArg(x)) => f.write_fmt(format_args!("unsuitable type for splatting: {}", x)),
            Self::TypeMismatch(TypeMismatch::SplatList(x)) => f.write_fmt(format_args!("unsuitable type for splatting: {}", x)),
            Self::TypeMismatch(TypeMismatch::SplatMap(x)) => f.write_fmt(format_args!("unsuitable type for splatting: {}", x)),
            Self::TypeMismatch(TypeMismatch::UnOp(x, op)) => f.write_fmt(format_args!("unsuitable type for '{}': {}", op, x)),

            Self::Value(Value::TooLarge) => f.write_str("value too large"),
            Self::Value(Value::TooLong) => f.write_str("value too long"),
            Self::Value(Value::OutOfRange) => f.write_str("value out of range"),
            Self::Value(Value::Convert(t)) => f.write_fmt(format_args!("couldn't convert to {}", t)),

            Self::FileSystem(FileSystem::NoParent(p)) => f.write_fmt(format_args!("path has no parent: {}", p.display())),
            Self::FileSystem(FileSystem::Read(p)) => f.write_fmt(format_args!("couldn't read file: {}", p.display())),

            Self::UnknownImport(p) => f.write_fmt(format_args!("unknown import: '{}'", p)),
        }
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assign => f.write_str("assigning"),
            Self::Bind => f.write_str("pattern matching"),
            Self::Evaluate => f.write_str("evaluating"),
            Self::Format => f.write_str("interpolating"),
            Self::Import => f.write_str("importing"),
            Self::Iterate => f.write_str("iterating"),
            Self::LookupName => f.write_str("evaluating"),
            Self::Parse => f.write_str("parsing"),
            Self::Slurp => f.write_str("slurping"),
            Self::Splat => f.write_str("splatting"),
        }
    }
}

impl<'a> Display for ErrorRenderer<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ErrorRenderer(err, code) = self;

        f.write_fmt(format_args!("Error: {}", err.reason.as_ref().unwrap_or(&Reason::None)))?;
        if let Some(locs) = err.locations.as_ref() {
            for (loc, act) in locs.iter() {
                let Location { offset, line, length } = loc;
                let col = code[0..*offset].rfind('\n').map(|x| offset - x - 1).unwrap_or(*offset);
                let bol = offset - col;
                let eol = code[bol+1..].find('\n').map(|x| x + bol + 1).unwrap_or(code.len());
                let span_end = min(offset + length, eol) - offset;
                f.write_char('\n')?;
                f.write_str(&code[bol..eol])?;
                f.write_char('\n')?;
                for _ in 0..col {
                    f.write_char(' ')?;
                }
                for _ in 0..span_end {
                    f.write_char('^')?;
                }
                f.write_fmt(format_args!("\nwhile {} at {}:{}", act, line, col))?;
            }
        }

        Ok(())
    }
}
