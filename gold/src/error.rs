use std::cmp::min;
use std::ops::{Range, Sub};

use std::fmt::{Debug, Display, Write};
use std::path::PathBuf;

use serde::{Serialize, Deserialize};

use crate::ast::{BinOp, UnOp};
use crate::lexing::TokenType;
use crate::object::{Key, Type};


/// Marks a position in a text buffer.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Position {
    offset: usize,
    line: u32,
    column: u32,
}

impl Position {
    /// Construct a new position from offset, line and column (all 0-indexed).
    pub fn new(offset: usize, line: u32, column: u32) -> Position {
        Position { offset, line, column }
    }

    /// Construct a new position pointing to the beginning of a buffer.
    pub fn zero() -> Position {
        Position {
            offset: 0,
            line: 0,
            column: 0,
        }
    }

    /// Add a positive displacement to a position and return a new one.
    ///
    /// Use `adjust(offset, 0)` to move within a line. Use `adjuct(offset, n)`
    /// to move to the beginning of a line.
    ///
    /// Do NOT use this method to jump to the middle of a new line. To do that,
    /// compose two calls to `adjust`.
    pub fn adjust(&self, offset: usize, delta_line: u32) -> Position {
        Position {
            offset: self.offset + offset,
            line: self.line + delta_line,
            column: if delta_line > 0 { 0 } else { self.column + offset as u32 }
        }
    }

    /// Return the zero-indexed offset into the buffer.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Return the zero-indexed line number.
    pub fn line(&self) -> u32 {
        self.line
    }

    /// Return the zero-indexed column number.
    pub fn column(&self) -> u32 {
        self.column
    }

    /// Return a new span starting at this position with a certain length.
    pub fn with_length(&self, length: usize) -> Span {
        Span { start: *self, length }
    }

    /// Return a new position by changing the line number.
    pub fn with_line(self, line: u32) -> Position {
        Position {
            offset: self.offset,
            column: self.column,
            line,
        }
    }

    /// Return a new position by changing the column number.
    pub fn with_column(self, col: u32) -> Position {
        Position {
            offset: self.offset,
            line: self.line,
            column: col,
        }
    }
}

impl Sub<Position> for Position {
    type Output = Span;

    /// Create a span marking the interval between two positions.
    fn sub(self, rhs: Position) -> Self::Output {
        rhs.with_length(self.offset - rhs.offset)
    }
}


/// Mark an interval of text in a buffer starting at a `Position` with a length.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Span {
    start: Position,
    length: usize,
}

impl Span {
    /// The starting position if the text span.
    pub fn start(&self) -> Position {
        self.start
    }

    /// The offset of the start of the span into the buffer.
    pub fn offset(&self) -> usize {
        self.start.offset
    }

    /// The zero-indexed line number of the start of the span.
    pub fn line(&self) -> u32 {
        self.start.line
    }

    /// The zero-indexed column number of the start of the span.
    pub fn column(&self) -> u32 {
        self.start.column
    }

    /// The length of the span.
    pub fn length(&self) -> usize {
        self.length
    }

    /// Return a new span by changing the line number.
    pub(crate) fn with_line(self, line: u32) -> Self {
        Span {
            start: self.start.with_line(line),
            length: self.length
        }
    }

    /// Return a new span by changing the column number.
    pub(crate) fn with_column(self, col: u32) -> Self {
        Span {
            start: self.start.with_column(col),
            length: self.length
        }
    }

    /// Return a new span by changing the line and column numbers.
    pub(crate) fn with_coord(self, line: u32, col: u32) -> Self {
        self.with_line(line).with_column(col)
    }
}

impl From<Range<u32>> for Span {
    /// Convert a range of offsets to a text span, assuming the interval begins
    /// on the first line. Use `with_line` if not.
    fn from(value: Range<u32>) -> Self {
        Span {
            start: Position::new(value.start as usize, 0, value.start),
            length: (value.end - value.start) as usize,
        }
    }
}

impl From<usize> for Span {
    /// Convert an offset to a text span with length one, assuming the interval
    /// begins on the first line. Use `with_line` if not.
    fn from(value: usize) -> Self {
        Span {
            start: Position::new(value, 0, value as u32),
            length: 1,
        }
    }
}


#[derive(Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Tagged<T> {
    span: Span,
    contents: T,
}

impl<T> Tagged<T> {
    pub fn new(location: Span, contents: T) -> Tagged<T> {
        Tagged::<T> {
            span: location,
            contents,
        }
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn unwrap(self) -> T {
        self.contents
    }

    pub fn with_line(self, line: u32) -> Tagged<T> {
        let loc = self.span.with_line(line);
        self.retag(loc)
    }

    pub fn with_column(self, col: u32) -> Tagged<T> {
        let loc = self.span.with_column(col);
        self.retag(loc)
    }

    pub fn with_coord(self, line: u32, col: u32) -> Tagged<T> {
        let loc = self.span.with_coord(line, col);
        self.retag(loc)
    }

    pub fn map<F, U>(self, f: F) -> Tagged<U> where F: FnOnce(T) -> U {
        Tagged::<U> {
            span: self.span,
            contents: f(self.contents),
        }
    }

    pub fn wraptag<F, U>(self, f: F) -> Tagged<U> where F: FnOnce(Tagged<T>) -> U {
        Tagged::<U> {
            span: self.span,
            contents: f(self),
        }
    }

    pub fn wrap<F, U, V>(self, f: F, loc: V) -> Tagged<U>
    where
        F: FnOnce(Tagged<T>) -> U,
        Span: From<V>
    {
        Tagged::<U> {
            span: Span::from(loc),
            contents: f(self),
        }
    }

    pub fn retag<U>(self, loc: U) -> Tagged<T>
    where
        Span: From<U>,
    {
        Tagged::<T> {
            span: Span::from(loc),
            contents: self.contents,
        }
    }

    pub fn tag_error(&self, action: Action) -> impl Fn(Error) -> Error {
        let loc = self.span();
        move |err: Error| err.tag(loc, action)
    }
}

impl<X, Y> Tagged<Result<X,Y>> {
    pub fn transpose(self) -> Result<Tagged<X>,Y> {
        match self.contents {
            Ok(x) => Ok(Tagged { span: self.span, contents: x }),
            Err(y) => Err(y),
        }
    }
}

impl<X> Tagged<Option<X>> {
    pub fn transpose(self) -> Option<Tagged<X>> {
        match self.contents {
            Some(x) => Some(Tagged { span: self.span, contents: x }),
            None => None,
        }
    }
}

impl<T: Debug> Debug for Tagged<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.contents.fmt(f)?;
        let span = self.span;
        f.write_fmt(format_args!(".tag({}:{}, {}..{})", span.line() + 1, span.column() + 1, span.offset(), span.offset() + span.length()))
    }
}

impl<T> AsRef<T> for Tagged<T> {
    fn as_ref(&self) -> &T {
        &self.contents
    }
}

impl<T> From<&Tagged<T>> for Span {
    fn from(value: &Tagged<T>) -> Self {
        value.span
    }
}

impl From<Range<Span>> for Span {
    fn from(value: Range<Span>) -> Self {
        Span {
            start: value.start.start(),
            length: value.end.offset() + value.end.length() - value.start.offset(),
        }
    }
}


#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SyntaxError(pub Position, pub Option<Syntax>);

impl SyntaxError {
    pub fn to_error(self) -> Error {
        let SyntaxError(pos, reason) = self;
        Error {
            locations: Some(vec![(pos.with_length(0), Action::Parse)]),
            reason: reason.map(Reason::Syntax),
            rendered: None,
        }
    }
}


#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SyntaxElement {
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
    Number,
    Operand,
    PosParam,

    // Other
    Whitespace,

    // Tokens
    Token(TokenType),
}

impl From<TokenType> for SyntaxElement {
    fn from(value: TokenType) -> Self {
        Self::Token(value)
    }
}


#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Syntax {
    UnexpectedEof,
    UnexpectedChar(char),
    ExpectedToken(TokenType),
    ExpectedOne(SyntaxElement),
    ExpectedTwo(SyntaxElement, SyntaxElement),
    ExpectedThree(SyntaxElement, SyntaxElement, SyntaxElement),
    MultiSlurp,
}

impl<T> From<T> for Syntax where SyntaxElement: From<T> {
    fn from(value: T) -> Self {
        Self::ExpectedOne(SyntaxElement::from(value))
    }
}

impl<T> From<(T,)> for Syntax where SyntaxElement: From<T> {
    fn from((value,): (T,)) -> Self {
        Self::ExpectedOne(SyntaxElement::from(value))
    }
}

impl<T,U> From<(T,U)> for Syntax where SyntaxElement: From<T> + From<U> {
    fn from((x,y): (T,U)) -> Self {
        Self::ExpectedTwo(SyntaxElement::from(x), SyntaxElement::from(y))
    }
}

impl<T,U,V> From<(T,U,V)> for Syntax where SyntaxElement: From<T> + From<U> + From<V> {
    fn from((x,y,z): (T,U,V)) -> Self {
        Self::ExpectedThree(SyntaxElement::from(x), SyntaxElement::from(y), SyntaxElement::from(z))
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
    pub locations: Option<Vec<(Span, Action)>>,
    pub reason: Option<Reason>,
    pub rendered: Option<String>,
}

impl Error {
    pub fn tag<T>(mut self, loc: T, action: Action) -> Self where Span: From<T> {
        match &mut self.locations {
            None => { self.locations = Some(vec![(Span::from(loc), action)]); },
            Some(vec) => { vec.push((Span::from(loc), action)); },
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
        match self {
            Self::ArgElement => f.write_str("function argument"),
            Self::As => f.write_str("'as'"),
            Self::Binding => f.write_str("binding pattern"),
            Self::Else => f.write_str("'else'"),
            Self::EndOfInput => f.write_str("end of input"),
            Self::Expression => f.write_str("expression"),
            Self::Identifier => f.write_str("identifier"),
            Self::ImportPath => f.write_str("import path"),
            Self::In => f.write_str("'in'"),
            Self::KeywordParam => f.write_str("keyword parameter"),
            Self::ListBindingElement => f.write_str("list binding pattern"),
            Self::ListElement => f.write_str("list element"),
            Self::MapBindingElement => f.write_str("map binding pattern"),
            Self::MapElement => f.write_str("map element"),
            Self::MapValue => f.write_str("map value"),
            Self::Number => f.write_str("number"),
            Self::Operand => f.write_str("operand"),
            Self::PosParam => f.write_str("positional parameter"),
            Self::Then => f.write_str("'then'"),
            Self::Whitespace => f.write_str("whitespace"),
            Self::Token(t) => f.write_fmt(format_args!("{}", t)),
        }
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

            Self::Syntax(Syntax::UnexpectedEof) => f.write_str("unexpected end of input"),
            Self::Syntax(Syntax::UnexpectedChar(c)) => f.write_fmt(format_args!("unexpected {}", c)),
            Self::Syntax(Syntax::ExpectedToken(x)) => f.write_fmt(format_args!("expected {}", x)),
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
                let bol = loc.offset() - loc.column() as usize;
                let eol = code[bol+1..].find('\n').map(|x| x + bol + 1).unwrap_or(code.len());
                let span_end = min(loc.offset() + loc.length(), eol) - loc.offset();
                f.write_char('\n')?;
                f.write_str(&code[bol..eol])?;
                f.write_char('\n')?;
                for _ in 0..loc.column() {
                    f.write_char(' ')?;
                }
                for _ in 0..span_end {
                    f.write_char('^')?;
                }
                f.write_fmt(format_args!("\nwhile {} at {}:{}", act, loc.line() + 1, loc.column() + 1))?;
            }
        }

        Ok(())
    }
}
