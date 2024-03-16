use std::cmp::min;
use std::ops::{Deref, Range, Sub};

use std::fmt::{Debug, Display, Write};
use std::path::PathBuf;

use gc::{custom_trace, Finalize, Trace};
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
    /// The starting position in the text span.
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


/// A wrapper for marking any object with a text span pointing to its origin in
/// a source file.
///
/// The AST (see ast.rs) makes heavy use of Tagged objects, so that errors can
/// be accurately reported.
#[derive(Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Tagged<T> {
    span: Span,
    contents: T,
}

impl<T> Tagged<T> {
    /// Construct a new Tagged wrapper.
    pub fn new(location: Span, contents: T) -> Tagged<T> {
        Tagged::<T> {
            span: location,
            contents,
        }
    }

    /// Return the text span.
    pub fn span(&self) -> Span {
        self.span
    }

    /// Destroy the wrapper and return its contents.
    pub fn unwrap(self) -> T {
        self.contents
    }

    /// Wrapper for [`Span::with_line`].
    pub fn with_line(self, line: u32) -> Tagged<T> {
        let loc = self.span.with_line(line);
        self.retag(loc)
    }

    /// Wrapper for [`Span::with_column`].
    pub fn with_column(self, col: u32) -> Tagged<T> {
        let loc = self.span.with_column(col);
        self.retag(loc)
    }

    /// Wrapper for [`Span::with_coord`].
    pub fn with_coord(self, line: u32, col: u32) -> Tagged<T> {
        let loc = self.span.with_coord(line, col);
        self.retag(loc)
    }

    /// Map the wrapped object and return a new tagged wrapper.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Tagged<U>
    {
        Tagged::<U> {
            span: self.span,
            contents: f(self.contents),
        }
    }

    /// Map the whole tagged object and return a new tagged wrapper.
    ///
    /// Useful for creating longer layers of tagged objects.
    pub fn wrap<U>(self, f: impl FnOnce(Tagged<T>) -> U) -> Tagged<U>
    {
        Tagged::<U> {
            span: self.span,
            contents: f(self),
        }
    }

    /// Substitute the text span with a new one.
    pub fn retag<U>(self, loc: U) -> Tagged<T>
    where
        Span: From<U>,
    {
        Tagged::<T> {
            span: Span::from(loc),
            contents: self.contents,
        }
    }

    /// Return a function that can apply a tag to error objects.
    ///
    /// Useful for `Result<_, Error>::map_err(result, _.tag_error(...))`
    pub fn tag_error(&self, action: Action) -> impl Fn(Error) -> Error {
        let span = self.span();
        move |err: Error| err.tag(span, action)
    }
}

unsafe impl<T: Trace> Trace for Tagged<T> {
    custom_trace!(this, { mark(&this.contents); });
}

impl<T: Finalize> Finalize for Tagged<T> {
    fn finalize(&self) {
        self.contents.finalize();
    }
}

impl<T: Debug> Debug for Tagged<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.contents.fmt(f)?;
        let span = self.span;
        f.write_fmt(format_args!(".tag({}:{}, {}..{})", span.line() + 1, span.column() + 1, span.offset(), span.offset() + span.length()))
    }
}

impl<T> Deref for Tagged<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

impl<T> AsRef<T> for Tagged<T> {
    fn as_ref(&self) -> &T {
        &self.contents
    }
}

impl<T> From<&Tagged<T>> for Span {
    fn from(value: &Tagged<T>) -> Self {
        value.span()
    }
}

impl From<Range<Span>> for Span {
    fn from(Range { start, end }: Range<Span>) -> Self {
        Span {
            start: start.start(),
            length: end.offset() + end.length() - start.offset(),
        }
    }
}


/// General error type used by both parsing and lexing.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SyntaxError {
    position: Position,
    reason: Option<Syntax>,
}

impl SyntaxError {
    /// Create a new syntax error.
    pub fn new(position: Position, reason: Option<Syntax>) -> SyntaxError {
        SyntaxError { position, reason }
    }

    /// Convert to the general error type.
    pub fn to_error(self) -> Error {
        let SyntaxError { position, reason } = self;
        Error {
            locations: Some(vec![(position.with_length(0), Action::Parse)]),
            reason: reason.map(Reason::Syntax),
            rendered: None,
        }
    }
}


/// A complete enumeration of all grammatical elements in the Gold language,
/// including tokens as well as composite structures.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SyntaxElement {
    /// The keyword 'as'
    As,

    /// The keyword 'else'
    Else,

    /// The keyword 'in'
    In,

    /// The keyword 'then'
    Then,

    /// A function argument
    ArgElement,

    /// A binding (otherwise known as a destructuring pattern)
    Binding,

    /// End of input stream
    EndOfInput,

    /// An expression
    Expression,

    /// An identifier ('variable' name)
    Identifier,

    /// Path of imported object
    ImportPath,

    /// A named keyword function parameter
    KeywordParam,

    /// An element of a list binding (any binding or a slurp)
    ListBindingElement,

    /// An element of a list (expressions, splats, conditional or looped
    /// elements)
    ListElement,

    /// An element of a map binding (any binding or a slurp)
    MapBindingElement,

    /// An element of a map (key-value expressions, splats, conditional or
    /// looped elements)
    MapElement,

    /// The value of a map item (after a key)
    MapValue,

    /// A number
    Number,

    /// An operand corresponding to an operator
    Operand,

    /// A positional function parameter
    PosParam,

    /// Arbitrary whitespace
    Whitespace,

    /// A lexical token
    Token(TokenType),
}

impl From<TokenType> for SyntaxElement {
    fn from(value: TokenType) -> Self {
        Self::Token(value)
    }
}


/// Enumerates all the possible reasons for a syntax error.
///
/// These reasons can be sourced from three different phases:
/// - lexing: the lexer was unable to recognize a token
/// - parsing: the token stream was illegal according to the grammar
/// - validation: additional AST integrity checks which for various reasons are
///   not desirable as part of the parser
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Syntax {
    /// Input ended too soon (thrown by the lexer)
    UnexpectedEof,

    /// An unexpected character (thrown by the lexer)
    UnexpectedChar(char),

    /// Expected a grammatical element but found another (thrown by the parser)
    ExpectedOne(SyntaxElement),

    /// Expected one of two grammatical element but found another (thrown by the parser)
    ExpectedTwo(SyntaxElement, SyntaxElement),

    /// Expected one of three grammatical element but found another (thrown by the parser)
    ExpectedThree(SyntaxElement, SyntaxElement, SyntaxElement),

    /// Multiple slurps in one collection (thrown by the validator)
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


/// Enumerates possible reasons for internal errors (which shouldn't happen).
#[derive(Debug, Clone, PartialEq)]
pub enum Internal {
    /// Gold attempted to bind a name in a frozen (immutable) namespace.
    SetInFrozenNamespace,
}


/// Enumerates possible binding types.
#[derive(Debug, Clone, PartialEq)]
pub enum BindingType {
    /// Bind a value to an identifier.
    Identifier,

    /// Bind a list of values to a list of patterns.
    List,

    /// Bind a mapping of values to a list of named patterns.
    Map,
}


/// Enumerates different reasons why unpacking might fail.
#[derive(Debug, Clone, PartialEq)]
pub enum Unpack {
    /// The list was too short - expected more values.
    ListTooShort,

    /// The list was too long - expected more binding patterns.
    ListTooLong,

    /// The map was missing a key.
    KeyMissing(Key),

    /// The binding type did not correspond to the object type (e.g. a list
    /// binding with a map object).
    TypeMismatch(BindingType, Type)
}


/// Enumerates different type mismatch reasons.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeMismatch {
    /// Attempted to iterate over a non-iterable.
    Iterate(Type),

    /// Attempted to splat a non-list into a list.
    SplatList(Type),

    /// Attempted to splat a non-map into a map.
    SplatMap(Type),

    /// Attempted to splat a non-list or a non-map into a function call.
    SplatArg(Type),

    /// Attempted to use a non-string as a map key.
    MapKey(Type),

    /// Attempted to string interpolate an exotic type.
    Interpolate(Type),

    /// Attempted to interpolate a type with the wrong format spec.
    InterpolateSpec(Type),

    /// Two types were incompatible with a binary operator.
    BinOp(Type, Type, BinOp),

    /// A type was incompatible with a unary operator.
    UnOp(Type, UnOp),

    /// Attempted to call a non-function.
    Call(Type),

    /// Attempted to convert a non-JSON type to JSON.
    Json(Type),

    /// Expected a positional function parameter to have a certain type, but it didn't.
    ExpectedPosArg {
        /// The zero-based index of the parameter.
        index: usize,

        /// Allowed types.
        allowed: Vec<Type>,

        /// Actual type received in function call.
        received: Type,
    },

    /// Expected a keyword function parameter to have a certain type, but it didn't.
    ExpectedKwArg {
        /// The name of the parameter.
        name: String,

        /// Allowed types.
        allowed: Vec<Type>,

        /// Actual type received in function call.
        received: Type,
    },

    /// Expected the number of arguments to fall in a certain range, but it didn't.
    ArgCount {
        /// Lower bound on number of arguments.
        low: usize,

        /// Upper bound on number of arguments.
        high: usize,

        /// Number of arguments received.
        received: usize,
    },
}


/// Enumerates different value-based error reasons.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Value was out of range.
    OutOfRange,

    /// Value was too large.
    TooLarge,

    /// Value was too long
    TooLong,

    /// Unable to convert value to a given type.
    Convert(Type),
}


/// Enumerates different file system error reasons.
#[derive(Debug, Clone, PartialEq)]
pub enum FileSystem {
    /// The file path has no parent (that is, no directory - unclear if this one
    /// will ever actully happen).
    NoParent(PathBuf),

    /// Unable to read from file.
    Read(PathBuf),
}


/// Grand enumeration of all possible error reasons.
#[derive(Debug, PartialEq)]
pub enum Reason {
    /// Unknown reason - should never happen.
    None,

    /// Syntax error.
    Syntax(Syntax),

    /// A name was unbound.
    Unbound(Key),

    /// A key was not assigned to a value.
    Unassigned(Key),

    /// Unpacking (pattern matching) error.
    Unpack(Unpack),

    /// Internal error - should never happen.
    Internal(Internal),

    /// Error received from external source, e.g. function call into other
    /// ecosystems.
    External(String),

    /// Type mismatch errors.
    TypeMismatch(TypeMismatch),

    /// Value-based errors (type was correct).
    Value(Value),

    /// File system errors.
    FileSystem(FileSystem),

    /// Import errors.
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


/// Enumerates all different 'actions' - things that Gold might try to do which
/// can cause an error.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Action {
    /// Parsing phase.
    Parse,

    /// Looking up an identifier in a namespace.
    LookupName,

    /// Binding a value to a pattern.
    Bind,

    /// Slurping a value into a collection.
    Slurp,

    /// Splatting a value into a collection.
    Splat,

    /// Iterate over a value.
    Iterate,

    /// Assign a key to a value.
    Assign,

    /// Importing an object.
    Import,

    /// Evaluating an expression.
    Evaluate,

    /// Interpolate a value into a string.
    Format,
}


/// The general error type of Gold.
#[derive(Debug, PartialEq, Default)]
pub struct Error {
    /// Stack trace of locations where the error happened.
    pub locations: Option<Vec<(Span, Action)>>,

    /// Reason for the error.
    pub reason: Option<Reason>,

    /// Human friendly string representation.
    pub rendered: Option<String>,
}

impl Error {
    /// Append a location to the stack. Takes ownership and returns the same
    /// object, for ease of use with `Result::map_err`.
    pub fn tag<T>(mut self, loc: T, action: Action) -> Self where Span: From<T> {
        match &mut self.locations {
            None => { self.locations = Some(vec![(Span::from(loc), action)]); },
            Some(vec) => { vec.push((Span::from(loc), action)); },
        }
        self
    }

    /// Construct a new error with an empty stack.
    pub fn new<T>(reason: T) -> Self where Reason: From<T> {
        Self {
            locations: None,
            reason: Some(Reason::from(reason)),
            rendered: None,
        }
    }

    /// Construct error with the 'unboud name' reason.
    pub fn unbound(key: Key) -> Self {
        Self::new(Reason::Unbound(key))
    }

    /// Remove the human-friendly string representation.
    pub fn unrender(self) -> Self {
        Self {
            locations: self.locations,
            reason: self.reason,
            rendered: None,
        }
    }

    /// Add a human-friendly string representation.
    pub fn render(self, code: Option<&str>) -> Self {
        let rendered = format!("{}", ErrorRenderer(&self, code));
        Self {
            locations: self.locations,
            reason: self.reason,
            rendered: Some(rendered),
        }
    }
}

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

fn fmt_expected_arg(f: &mut std::fmt::Formatter, name: impl Display, allowed: &Vec<Type>, received: &Type) -> std::fmt::Result {
    f.write_fmt(format_args!("unsuitable type for parameter {} - expected ", name))?;
    match allowed[..] {
        [] => {},
        [t] => f.write_fmt(format_args!("{}", t))?,
        _ => {
            let s = allowed[0..allowed.len() - 1].iter().map(|t| format!("{}", t)).collect::<Vec<String>>().join(", ");
            f.write_fmt(format_args!("{} or {}", s, allowed.last().unwrap()))?
        }
    }
    f.write_fmt(format_args!(", got {}", received))
}

impl Display for Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::None => f.write_str("unknown reason - this should not happen, please file a bug report"),

            Self::Syntax(Syntax::UnexpectedEof) => f.write_str("unexpected end of input"),
            Self::Syntax(Syntax::UnexpectedChar(c)) => f.write_fmt(format_args!("unexpected {}", c)),
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

            Self::TypeMismatch(TypeMismatch::ArgCount{ low, high, received }) => {
                if low == high && *high == 1 {
                    f.write_fmt(format_args!("expected 1 argument, got {}", received))
                } else if low == high {
                    f.write_fmt(format_args!("expected {} arguments, got {}", low, received))
                } else {
                    f.write_fmt(format_args!("expected {} to {} arguments, got {}", low, high, received))
                }
            },
            Self::TypeMismatch(TypeMismatch::BinOp(l, r, op)) => f.write_fmt(format_args!("unsuitable types for '{}': {} and {}", op, l, r)),
            Self::TypeMismatch(TypeMismatch::Call(x)) => f.write_fmt(format_args!("unsuitable type for function call: {}", x)),
            Self::TypeMismatch(TypeMismatch::ExpectedPosArg { index, allowed, received }) => fmt_expected_arg(f, index + 1, allowed, received),
            Self::TypeMismatch(TypeMismatch::ExpectedKwArg { name, allowed, received }) => fmt_expected_arg(f, name, allowed, received),
            Self::TypeMismatch(TypeMismatch::Interpolate(x)) => f.write_fmt(format_args!("unsuitable type for interpolation: {}", x)),
            Self::TypeMismatch(TypeMismatch::InterpolateSpec(x)) => f.write_fmt(format_args!("unsuitable type for format spec: {}", x)),
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


/// Utility struct for facilitating error rendering.
///
/// Has access to both the error and the code, so that it can just implement the
/// Display trait.
struct ErrorRenderer<'a>(&'a Error, Option<&'a str>);

impl<'a> Display for ErrorRenderer<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ErrorRenderer(err, code) = self;

        f.write_fmt(format_args!("Error: {}", err.reason.as_ref().unwrap_or(&Reason::None)))?;
        if let Some(locs) = err.locations.as_ref() {
            for (loc, act) in locs.iter() {
                if let Some(code) = code {
                    // Offset of the beginning of the line
                    let bol = loc.offset() - loc.column() as usize;

                    // Offset of the end of the line
                    let eol = code[bol+1..].find('\n').map(|x| x + bol + 1).unwrap_or(code.len());

                    // Offset of the end of the span to be displayed: either the end
                    // of the line (if longer than a line), or the end of the span
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
                }
                f.write_fmt(format_args!("\nwhile {} at {}:{}", act, loc.line() + 1, loc.column() + 1))?;
            }
        }

        Ok(())
    }
}
