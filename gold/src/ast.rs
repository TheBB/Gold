use std::collections::HashSet;
use std::fmt::Display;
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::error::{PatternType, Syntax};

use super::error::{Error, Tagged, Action};
use super::object::{Object, Key};
use super::traits::{Boxable, Free, FreeImpl, FreeAndBound, Validatable, Taggable, ToVec, HasSpan};


/// Utility function for collecting free and bound names from a binding element
/// with a potential default value.
fn binding_element_free_and_bound(
    binding: &impl FreeAndBound,
    default: Option<&impl Free>,
    free: &mut HashSet<Key>,
    bound: &mut HashSet<Key>,
) {
    if let Some(expr) = default {
        for ident in expr.free() {
            if !bound.contains(&ident) {
                free.insert(ident);
            }
        }
    }
    binding.free_and_bound(free, bound)
}


// ListBindingElement
// ----------------------------------------------------------------

/// A list binding element is anything that is legal inside a list pattern.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ListPatternElement {

    /// An ordinary binding with potential default value
    Binding {
        binding: Tagged<Binding>,
        default: Option<Tagged<Expr>>,
    },

    /// Slurp into a named list
    SlurpTo(Tagged<Key>),

    /// Slurp but discard values
    Slurp,
}

impl Validatable for ListPatternElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ListPatternElement::Binding { binding, default } => {
                binding.validate()?;
                if let Some(node) = default {
                    node.validate()?;
                }
            },
            _ => {},
        }
        Ok(())
    }
}

impl FreeAndBound for ListPatternElement {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            ListPatternElement::Binding { binding, default } => {
                binding_element_free_and_bound(binding, default.as_ref(), free, bound);
            },
            ListPatternElement::SlurpTo(name) => { bound.insert(**name); },
            _ => {},
        }
    }
}


// MapBindingElement
// ----------------------------------------------------------------

/// A map binding element is anything that is legan inside a map pattern.
///
/// Since map bindings discard superfluous values by default, there's no need
/// for an anonymous slurp.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MapPatternElement {

    /// An ordinary binding with potential default value.
    Binding {
        key: Tagged<Key>,
        binding: Tagged<Binding>,
        default: Option<Tagged<Expr>>,
    },

    /// Slurp into a named map.
    SlurpTo(Tagged<Key>),
}

impl FreeAndBound for MapPatternElement {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            MapPatternElement::Binding { key: _, binding, default } => {
                binding_element_free_and_bound(binding, default.as_ref(), free, bound);
            },
            MapPatternElement::SlurpTo(name) => { bound.insert(**name); },
        }
    }
}

impl Validatable for MapPatternElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            MapPatternElement::Binding { binding, default, .. } => {
                binding.validate()?;
                if let Some(node) = default {
                    node.validate()?;
                }
            },
            _ => {},
        }
        Ok(())
    }
}


// ListBinding
// ----------------------------------------------------------------

/// A list binding destructures a list into a list of patterns.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ListBinding(pub Vec<Tagged<ListPatternElement>>);

impl FreeAndBound for ListBinding {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        for element in &self.0 {
            element.free_and_bound(free, bound);
        }
    }
}

impl Validatable for ListBinding {
    fn validate(&self) -> Result<(), Error> {
        let mut found_slurp = false;
        for element in &self.0 {
            element.validate()?;

            // It's illegal to have more than one slurp in a list binding.
            if let ListPatternElement::Binding { .. } = **element { }
            else {
                if found_slurp {
                    return Err(Error::new(Syntax::MultiSlurp).tag(element, Action::Parse))
                }
                found_slurp = true;
            }
        }
        Ok(())
    }
}


// MapBinding
// ----------------------------------------------------------------

/// A map binding destructres a map into a list of patterns associated with
/// keys.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MapBinding(pub Vec<Tagged<MapPatternElement>>);

impl FreeAndBound for MapBinding {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        for element in &self.0 {
            element.free_and_bound(free, bound);
        }
    }
}

impl Validatable for MapBinding {
    fn validate<'a>(&'a self) -> Result<(), Error> {
        let mut found_slurp = false;
        for element in &self.0 {
            element.validate()?;

            // It's illegal to have more than one slurp in a map binding.
            if let MapPatternElement::SlurpTo(_) = **element {
                if found_slurp {
                    return Err(Error::new(Syntax::MultiSlurp).tag(element, Action::Parse))
                }
                found_slurp = true;
            }
        }
        Ok(())
    }
}


// Pattern
// ----------------------------------------------------------------

/// A pattern comes in three flavors: identifiers (which don't do any
/// destructuring), and list and map bindings, which destructures lists and maps
/// respectively.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Pattern {
    Identifier(Tagged<Key>),
    List(Tagged<ListBinding>),
    Map(Tagged<MapBinding>),
}

impl Pattern {
    /// Return the type of the binding.
    pub fn type_of(&self) -> PatternType {
        match self {
            Self::Identifier(_) => PatternType::Identifier,
            Self::List(_) => PatternType::List,
            Self::Map(_) => PatternType::Map,
        }
    }

    /// Return the identifier, if applicable.
    pub fn identifier(&self) -> Option<Tagged<Key>> {
        match self {
            Self::Identifier(x) => Some(*x),
            _ => None,
        }
    }
}

impl FreeAndBound for Pattern {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            Pattern::Identifier(name) => { bound.insert(**name); },
            Pattern::List(elements) => elements.free_and_bound(free, bound),
            Pattern::Map(elements) => elements.free_and_bound(free, bound),
        }
    }
}

impl Validatable for Pattern {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Pattern::List(elements) => elements.validate(),
            Pattern::Map(elements) => elements.validate(),
            _ => Ok(()),
        }
    }
}


// Binding
// ----------------------------------------------------------------

/// A binding is a pattern associated with an optional type expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Binding {
    pub pattern: Tagged<Pattern>,
    pub tp: Option<Tagged<TypeExpr>>,
}

impl Binding {
    /// Return the identifier, if applicable.
    pub fn identifier(&self) -> Option<Tagged<Key>> {
        self.pattern.identifier()
    }
}

impl Validatable for Binding {
    fn validate(&self) -> Result<(), Error> {
        self.pattern.validate()?;
        if let Some(tp) = &self.tp {
            tp.validate()?;
        }
        Ok(())
    }
}

impl FreeAndBound for Binding {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        self.pattern.free_and_bound(free, bound)
    }
}


// StringElement
// ----------------------------------------------------------------

/// A string element is anything that is legal in a string: either raw string
/// data or an interpolated expression. A string is represented as a li of
/// string elements.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum StringElement {
    Raw(Arc<str>),
    Interpolate(Tagged<Expr>),
}

impl StringElement {
    /// Construct a raw string element.
    pub fn raw<T: AsRef<str>>(val: T) -> StringElement {
        StringElement::Raw(Arc::from(val.as_ref()))
    }
}

impl Validatable for StringElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            StringElement::Interpolate(node) => { node.validate()?; }
            _ => {},
        }
        Ok(())
    }
}


// ListElement
// ----------------------------------------------------------------

/// A list element is anything that is legal inside a list literal:
/// - singleton elements
/// - splatted expressions
/// - iterated elements
/// - conditional elements
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ListElement {
    Singleton(Tagged<Expr>),
    Splat(Tagged<Expr>),
    Loop {
        binding: Tagged<Binding>,
        iterable: Tagged<Expr>,
        element: Box<Tagged<ListElement>>,
    },
    Cond {
        condition: Tagged<Expr>,
        element: Box<Tagged<ListElement>>,
    },
}

impl FreeImpl for ListElement {
    fn free_impl(&self, free: &mut HashSet<Key>) {
        match self {
            ListElement::Singleton(expr) => expr.free_impl(free),
            ListElement::Splat(expr) => expr.free_impl(free),
            ListElement::Cond { condition, element } => {
                condition.free_impl(free);
                element.free_impl(free);
            },
            ListElement::Loop { binding, iterable, element } => {
                iterable.free_impl(free);
                let mut bound: HashSet<Key> = HashSet::new();
                binding.free_and_bound(free, &mut bound);
                for ident in element.free() {
                    if !bound.contains(&ident) {
                        free.insert(ident);
                    }
                }
            }
        }
    }
}

impl Validatable for ListElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ListElement::Singleton(node) => { node.validate()?; },
            ListElement::Splat(node) => { node.validate()?; },
            ListElement::Loop { binding, iterable, element } => {
                binding.validate()?;
                iterable.validate()?;
                element.validate()?;
            },
            ListElement::Cond { condition, element } => {
                condition.validate()?;
                element.validate()?;
            },
        }
        Ok(())
    }
}


// MapElement
// ----------------------------------------------------------------

/// A map element is anything that is legal in a map literal:
/// - singleton elements
/// - splatted expressions
/// - iterated elements
/// - conditional elements
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MapElement {
    Singleton {
        key: Tagged<Expr>,
        value: Tagged<Expr>,
    },
    Splat(Tagged<Expr>),
    Loop {
        binding: Tagged<Binding>,
        iterable: Tagged<Expr>,
        element: Box<Tagged<MapElement>>
    },
    Cond {
        condition: Tagged<Expr>,
        element: Box<Tagged<MapElement>>,
    },
}

impl FreeImpl for MapElement {
    fn free_impl(&self, free: &mut HashSet<Key>) {
        match self {
            MapElement::Singleton { key, value } => {
                key.free_impl(free);
                value.free_impl(free);
            },
            MapElement::Splat(expr) => expr.free_impl(free),
            MapElement::Cond { condition, element } => {
                condition.free_impl(free);
                element.free_impl(free);
            },
            MapElement::Loop { binding, iterable, element } => {
                iterable.free_impl(free);
                let mut bound: HashSet<Key> = HashSet::new();
                binding.free_and_bound(free, &mut bound);
                for ident in element.free() {
                    if !bound.contains(&ident) {
                        free.insert(ident);
                    }
                }
            }
        }
    }
}

impl Validatable for MapElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            MapElement::Singleton { key, value } => {
                key.validate()?;
                value.validate()?;
            },
            MapElement::Splat(node) => { node.validate()?; },
            MapElement::Loop { binding, iterable, element } => {
                binding.validate()?;
                iterable.validate()?;
                element.validate()?;
            },
            MapElement::Cond { condition, element } => {
                condition.validate()?;
                element.validate()?;
            },
        }
        Ok(())
    }
}


// ArgElement
// ----------------------------------------------------------------

/// An argument element is anything that is legal in a function call context:
/// - singleton positional arguments
/// - singleton keyword arguments
/// - splatted expressions
///
/// Currently, Gold does not support conditional or iterated arguments.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ArgElement {
    Singleton(Tagged<Expr>),
    Keyword(Tagged<Key>, Tagged<Expr>),
    Splat(Tagged<Expr>),
}

impl FreeImpl for ArgElement {
    fn free_impl(&self, free: &mut HashSet<Key>) {
        match self {
            ArgElement::Singleton(expr) => { expr.free_impl(free); },
            ArgElement::Splat(expr) => { expr.free_impl(free); },
            ArgElement::Keyword(_, expr) => { expr.free_impl(free); },
        }
    }
}

impl Validatable for ArgElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ArgElement::Singleton(node) => { node.validate()?; },
            ArgElement::Splat(node) => { node.validate()?; },
            ArgElement::Keyword(_, value) => { value.validate()?; },
        }
        Ok(())
    }
}


// Operator
// ----------------------------------------------------------------

/// Enumerates all the unary operators in the Gold language.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum UnOp {

    /// Passthrough (do-nothing) operator, e.g. the unary plus
    Passthrough,

    /// Arithmetical negation (unary minus)
    ArithmeticalNegate,

    /// Logical negation (unary 'not')
    LogicalNegate,
}

/// Enumerates all the binary operators in the Gold language.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum BinOp {

    /// Index or subscripting operator
    Index,

    /// Exponentiation
    Power,

    /// Multiplication
    Multiply,

    /// Integer division
    IntegerDivide,

    /// Mathematical division
    Divide,

    /// Addition
    Add,

    /// Subtraction
    Subtract,

    /// Less-than
    Less,

    /// Greater-than
    Greater,

    /// Less-than-or-equal-to
    LessEqual,

    /// Greater-than-or-equal-to
    GreaterEqual,

    /// Equality
    Equal,

    /// Inequality
    NotEqual,

    /// Logical conjunction
    And,

    /// Logical disjunction
    Or,
}

/// In Gold AST terms, a transform acts on a value and returns another. Thus,
/// all transform are of the form Expr -> Expr.
///
/// All unary and binary operators are realized as transforms. In an expression
/// such as x + y, the transform (+ y) acts on the 'operand' x.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Transform {

    /// Unary operator
    UnOp(Tagged<UnOp>),

    /// Binary operator with right operand
    BinOp(Tagged<BinOp>, Box<Tagged<Expr>>),

    /// Function call operator with arguments
    FunCall(Tagged<Vec<Tagged<ArgElement>>>),
}

impl Transform {
    /// Construct an index/subscripting transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn index(subscript: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Index.tag(loc), subscript.to_box())
    }

    /// Construct an exponentiation transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn power(exponent: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Power.tag(loc), exponent.to_box())
    }

    /// Construct a multiplication transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn multiply(multiplicand: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Multiply.tag(loc), multiplicand.to_box())
    }

    /// Construct an integer division transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn integer_divide(divisor: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::IntegerDivide.tag(loc), divisor.to_box())
    }

    /// Construct a mathematical division transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn divide(divisor: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Divide.tag(loc), divisor.to_box())
    }

    /// Construct an addition transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn add(addend: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Add.tag(loc), addend.to_box())
    }

    /// Construct a subtraction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn subtract(subtrahend: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Subtract.tag(loc), subtrahend.to_box())
    }

    /// Construct a less-than transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn less(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Less.tag(loc), rhs.to_box())
    }

    /// Construct a greater-than transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn greater(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Greater.tag(loc), rhs.to_box())
    }

    /// Construct a less-than-or-equal transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn less_equal(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::LessEqual.tag(loc), rhs.to_box())
    }

    /// Construct a greater-than-or-equal transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn greater_equal(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::GreaterEqual.tag(loc), rhs.to_box())
    }

    /// Construct an equality check transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn equal(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Equal.tag(loc), rhs.to_box())
    }

    /// Construct an inequality check transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn not_equal(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::NotEqual.tag(loc), rhs.to_box())
    }

    /// Construct a logical conjunction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn and(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::And.tag(loc), rhs.to_box())
    }

    /// Construct a logical disjunction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn or(rhs: Tagged<Expr>, loc: impl HasSpan) -> Transform {
        Transform::BinOp(BinOp::Or.tag(loc), rhs.to_box())
    }
}

impl Validatable for Transform {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Transform::BinOp(_, node) => { node.validate()?; },
            Transform::FunCall(args) => {
                for arg in args.as_ref() {
                    arg.validate()?;
                }
            },
            _ => {},
        }
        Ok(())
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Passthrough => f.write_str(""),
            Self::ArithmeticalNegate => f.write_str("-"),
            Self::LogicalNegate => f.write_str("not"),
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Index => f.write_str("subscript"),
            Self::Power => f.write_str("^"),
            Self::Multiply => f.write_str("*"),
            Self::IntegerDivide => f.write_str("//"),
            Self::Divide => f.write_str("/"),
            Self::Add => f.write_str("+"),
            Self::Subtract => f.write_str("-"),
            Self::Less => f.write_str("<"),
            Self::Greater => f.write_str(">"),
            Self::LessEqual => f.write_str("<="),
            Self::GreaterEqual => f.write_str(">="),
            Self::Equal => f.write_str("=="),
            Self::NotEqual => f.write_str("!="),
            Self::And => f.write_str("and"),
            Self::Or => f.write_str("or"),
        }
    }
}



// Expr
// ----------------------------------------------------------------

/// The most important AST node: an evaluatable expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {

    /// A literal object (usually numbers, booleans, null and strings).
    Literal(Object),

    /// A string as a vector of string elements (raw string data and
    /// interpolated expressions). During AST construction, a single raw string
    /// element is turned into a pure string literal.
    String(Vec<StringElement>),

    /// An identifier to be looked up by name.
    Identifier(Tagged<Key>),

    /// A list of list elements, see [`ListElement`].
    List(Vec<Tagged<ListElement>>),

    /// A map of (sequential) map elements, see [`ListElement`].
    Map(Vec<Tagged<MapElement>>),

    /// A let-binding block
    Let {

        /// List expressions to be bound to patterns.
        bindings: Vec<(Tagged<Binding>, Tagged<Expr>)>,

        /// Final expression whose value becomes the value of the whole block.
        expression: Box<Tagged<Expr>>,
    },

    /// An transformed expression, usually a binary operator applied to two
    /// operands, where the left operand is the input, and the operator and the
    /// right operand together form the transform.
    Transformed {

        /// The expression to act on.
        operand: Box<Tagged<Expr>>,

        /// The transform to apply, see [`Transform`].
        transform: Transform,
    },

    /// A function definition.
    Function {

        /// Optional type parameters.
        type_params: Option<Vec<Tagged<Key>>>,

        /// Positional function parameters.
        positional: ListBinding,

        /// Optional keyword parameters.
        keywords: Option<MapBinding>,

        /// Optional return type.
        return_type: Option<Tagged<TypeExpr>>,

        /// The expression to evaluate when called.
        expression: Box<Tagged<Expr>>,
    },

    /// A conditional branch. Gold doesn't have else-less branches.
    Branch {
        condition: Box<Tagged<Expr>>,
        true_branch: Box<Tagged<Expr>>,
        false_branch: Box<Tagged<Expr>>,
    }
}

impl Tagged<Expr> {
    /// Form a sum expression from two terms.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn add(self, addend: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::add(addend, loc))
    }

    /// Form a subtraction expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn sub(self, subtrahend: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::subtract(subtrahend, loc))
    }

    /// Form a multiplication expression from two factors.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn mul(self, multiplicand: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::multiply(multiplicand, loc))
    }

    /// Form a division expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn div(self, divisor: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::divide(divisor, loc))
    }

    /// Form an integer division expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn idiv(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::integer_divide(rhs, loc))
    }

    /// Form a less-than expression from operandsterms.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn lt(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::less(rhs, loc))
    }

    /// Form a greater-than expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn gt(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::greater(rhs, loc))
    }

    /// Form a less-than-or-equal expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn lte(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::less_equal(rhs, loc))
    }

    /// Form a greater-than-or-equal expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn gte(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::greater_equal(rhs, loc))
    }

    /// Form an equality check expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn equal(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::equal(rhs, loc))
    }

    /// Form an inequality check expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn not_equal(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::not_equal(rhs, loc))
    }

    /// Form a logical conjunction expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn and(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::and(rhs, loc))
    }

    /// Form a logical disjunction expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn or(self, rhs: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::or(rhs, loc))
    }

    /// Form an exponentiation expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn pow(self, exponent: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::power(exponent, loc))
    }

    /// Form a subscripting/indexing expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn index(self, subscript: Tagged<Expr>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::index(subscript, loc))
    }

    /// Arithmetically negate this expression.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn neg(self, loc: impl HasSpan) -> Expr {
        self.transform(Transform::UnOp(UnOp::ArithmeticalNegate.tag(loc)))
    }

    /// Logically negate this expression.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn not(self, loc: impl HasSpan) -> Expr {
        self.transform(Transform::UnOp(UnOp::LogicalNegate.tag(loc)))
    }

    /// Form the combined transformed expression from this operand and a transform.
    pub fn transform(self, op: Transform) -> Expr {
        Expr::Transformed {
            operand: self.to_box(),
            transform: op,
        }
    }

    /// Form a function call expression from by calling this function with a
    /// list of arguments.
    ///
    /// * `loc` - the location of the function call operator in the buffer.
    pub fn funcall(self, args: impl ToVec<Tagged<ArgElement>>, loc: impl HasSpan) -> Expr {
        self.transform(Transform::FunCall(args.to_vec().tag(loc)))
    }
}

impl Expr {
    /// Construct a list expression.
    pub fn list(elements: impl ToVec<Tagged<ListElement>>) -> Expr where {
        Expr::List(elements.to_vec())
    }

    /// Construct a map expression.
    pub fn map(x: impl ToVec<Tagged<MapElement>>) -> Expr {
        Expr::Map(x.to_vec())
    }

    /// Construct a string expression.
    ///
    /// If there's only one string element, and it's a raw string, (or if the
    /// string is empty) this will return a string literal.
    pub fn string(value: Vec<StringElement>) -> Expr {
        if value.len() == 0 {
            Expr::Literal(Object::str_interned(""))
        } else if let [StringElement::Raw(val)] = &value[..] {
            Expr::Literal(Object::str(val))
        } else {
            Expr::String(value)
        }
    }
}

impl FreeImpl for Expr {
    fn free_impl(&self, free: &mut HashSet<Key>) {
        match self {
            Expr::Literal(_) => {},
            Expr::String(elements) => {
                for element in elements {
                    if let StringElement::Interpolate(expr) = element {
                        expr.free_impl(free);
                    }
                }
            },
            Expr::Identifier(name) => { free.insert(**name); },
            Expr::List(elements) => {
                for element in elements {
                    element.free_impl(free);
                }
            },
            Expr::Map(elements) => {
                for element in elements {
                    element.free_impl(free);
                }
            },
            Expr::Let { bindings, expression } => {
                let mut bound: HashSet<Key> = HashSet::new();
                for (binding, expr) in bindings {
                    for id in expr.free() {
                        if !bound.contains(&id) {
                            free.insert(id);
                        }
                    }
                    binding.free_and_bound(free, &mut bound);
                }
                for id in expression.free() {
                    if !bound.contains(&id) {
                        free.insert(id);
                    }
                }
            },
            Expr::Transformed { operand, transform: operator } => {
                operand.free_impl(free);
                match operator {
                    Transform::BinOp(_, expr) => expr.free_impl(free),
                    Transform::FunCall(elements) => {
                        for element in elements.as_ref() {
                            element.free_impl(free);
                        }
                    }
                    _ => {},
                }
            },
            Expr::Branch { condition, true_branch, false_branch } => {
                condition.free_impl(free);
                true_branch.free_impl(free);
                false_branch.free_impl(free);
            },
            Expr::Function { positional, keywords, expression, .. } => {
                let mut bound: HashSet<Key> = HashSet::new();
                positional.free_and_bound(free, &mut bound);
                keywords.as_ref().map(|x| x.free_and_bound(free, &mut bound));
                for id in expression.free() {
                    if !bound.contains(&id) {
                        free.insert(id);
                    }
                }
            }
        }
    }
}

impl Validatable for Expr {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Expr::String(elements) => {
                for element in elements {
                    element.validate()?;
                }
            },
            Expr::List(elements) => {
                for element in elements {
                    element.validate()?;
                }
            },
            Expr::Map(elements) => {
                for element in elements {
                    element.validate()?;
                }
            },
            Expr::Let { bindings, expression } => {
                for (binding, node) in bindings {
                    binding.validate()?;
                    node.validate()?;
                }
                expression.validate()?;
            },
            Expr::Transformed { operand, transform: operator } => {
                operand.validate()?;
                operator.validate()?;
            },
            Expr::Function { positional, keywords, expression, return_type, .. } => {
                positional.validate()?;
                keywords.as_ref().map(MapBinding::validate).transpose()?;
                expression.validate()?;
                return_type.as_ref().map(|x| x.validate()).transpose()?;
            },
            Expr::Branch { condition, true_branch, false_branch } => {
                condition.validate()?;
                true_branch.validate()?;
                false_branch.validate()?;
            }
            _ => {},
        }
        Ok(())
    }
}


// TopLevel
// ----------------------------------------------------------------

/// A top-level AST node, only legal at the top level of a file.
#[derive(Debug)]
pub enum TopLevel {

    /// Import an object by loading another file and binding it to a pattern.
    Import(Tagged<String>, Tagged<Pattern>),

    /// Define a type
    TypeDef {
        name: Tagged<Key>,
        params: Option<Vec<Tagged<Key>>>,
        expr: Tagged<TypeExpr>,
    }
}

impl Validatable for TopLevel {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Self::Import(_, binding) => { binding.validate()?; },
            Self::TypeDef { expr, .. } => { expr.validate()?; },
        }
        Ok(())
    }
}


// File
// ----------------------------------------------------------------

/// The complete AST node of a file, consisting of a number of top-level
/// statements followed by an expression.
#[derive(Debug)]
pub struct File {

    /// Top-level statements.
    pub statements: Vec<TopLevel>,

    /// Final expression to evaluate.
    pub expression: Tagged<Expr>,
}

impl Validatable for File {
    fn validate(&self) -> Result<(), Error> {
        for statement in &self.statements {
            statement.validate()?;
        }
        self.expression.validate()?;
        Ok(())
    }
}



// TypeExpr
// ----------------------------------------------------------------

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum TypeExpr {

    /// Parametrized type
    Parametrized {
        name: Tagged<Key>,
        params: Option<Vec<Tagged<TypeExpr>>>,
    },
}

impl Validatable for TypeExpr {
    fn validate(&self) -> Result<(), Error> {
        Ok(())
    }
}
