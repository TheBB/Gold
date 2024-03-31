use std::rc::Rc;

use crate::{builtins::BUILTINS, error::{Reason, Span, Syntax}, types::LogicOp};
use crate::formatting::FormatSpec;

use crate::error::{Action, Error, Tagged, Taggable};
use crate::Object;
use crate::types::Key;
use super::low;
use super::scope::{SubScope, Scope, LocalScope};
use crate::types::{UnOp, BinOp, Res, EagerOp};

// Utility
// ----------------------------------------------------------------

trait Lower {
    type Target;
    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target>;
}

impl<T: Lower> Lower for Tagged<T> {
    type Target = Tagged<<T as Lower>::Target>;
    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        self.map(|t| t.lower(scope)).transpose()
    }
}

impl<T: Lower> Lower for Option<T> {
    type Target = Option<<T as Lower>::Target>;
    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        self.map(|t| t.lower(scope)).transpose()
    }
}

// ListBindingElement
// ----------------------------------------------------------------

/// A list binding element is anything that is legal inside a list pattern.
#[derive(Debug, Clone, PartialEq)]
pub enum ListBindingElement {
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

impl ListBindingElement {
    fn announce_bindings(&self, scope: &mut dyn SubScope) {
        match self {
            Self::Binding { binding, .. } => { binding.announce_bindings(scope); }
            Self::SlurpTo(name) => { scope.announce_binding(*name.as_ref()); }
            Self::Slurp => { }
        }
    }
}

// MapBindingElement
// ----------------------------------------------------------------

/// A map binding element is anything that is legan inside a map pattern.
///
/// Since map bindings discard superfluous values by default, there's no need
/// for an anonymous slurp.
#[derive(Debug, Clone, PartialEq)]
pub enum MapBindingElement {
    /// An ordinary binding with potential default value.
    Binding {
        key: Tagged<Key>,
        binding: Tagged<Binding>,
        default: Option<Tagged<Expr>>,
    },

    /// Slurp into a named map.
    SlurpTo(Tagged<Key>),
}

impl MapBindingElement {
    fn announce_bindings(&self, scope: &mut dyn SubScope) {
        match self {
            Self::Binding { binding, .. } => { binding.announce_bindings(scope); }
            Self::SlurpTo(name) => { scope.announce_binding(*name.as_ref()); }
        }
    }
}

// ListBinding
// ----------------------------------------------------------------

/// A list binding destructures a list into a list of patterns.
#[derive(Debug, Clone, PartialEq)]
pub struct ListBinding(Vec<Tagged<ListBindingElement>>);

impl ListBinding {
    pub fn new(elements: Vec<Tagged<ListBindingElement>>) -> Self {
        Self(elements)
    }

    fn announce_bindings(&self, scope: &mut dyn SubScope) {
        for element in &self.0 {
            element.announce_bindings(scope);
        }
    }
}

impl Lower for ListBinding {
    type Target = low::ListBinding;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        let mut retval = low::ListBinding::default();

        for element in self.0 {
            let (element, span) = element.decompose();
            match element {
                ListBindingElement::Binding { binding, default } => {
                    match (default.is_some(), retval.slurp) {
                        (true, Some(_)) => { retval.def_back += 1; }
                        (true, None) => { retval.def_front += 1; }
                        (false, Some(_)) => { retval.num_back += 1; }
                        (false, None) => { retval.num_front += 1; }
                    }

                    let new_default = default.lower(scope)?;
                    let new_binding = binding.lower(scope)?;
                    retval.push(new_binding, new_default);
                }
                _ => {
                    if retval.slurp.is_some() {
                        return Err(Error::new(Syntax::MultiSlurp).tag(span, Action::Parse));
                    }
                    if let ListBindingElement::SlurpTo(key) = element {
                        match scope.lookup_store(*key.as_ref()) {
                            None => {
                                return Err(Error::new(Reason::Unbound(*key.as_ref())).tag(key.span(), Action::LookupName));
                            }
                            Some(index) => {
                                retval.slurp = Some(Some(index));
                                continue;
                            },
                        }
                    } else {
                        retval.slurp = Some(None);
                    }
                }
            }
        }

        Ok(retval)
    }
}

// MapBinding
// ----------------------------------------------------------------

/// A map binding destructres a map into a list of patterns associated with
/// keys.
#[derive(Debug, Clone, PartialEq)]
pub struct MapBinding(Vec<Tagged<MapBindingElement>>);

impl MapBinding {
    pub fn new(elements: Vec<Tagged<MapBindingElement>>) -> Self {
        Self(elements)
    }

    fn announce_bindings(&self, scope: &mut dyn SubScope) {
        for element in &self.0 {
            element.announce_bindings(scope);
        }
    }
}

impl Lower for MapBinding {
    type Target = low::MapBinding;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        let mut retval = low::MapBinding {
            elements: Vec::new(),
            slurp: None,
        };

        for element in self.0 {
            let (element, span) = element.decompose();
            match element {
                MapBindingElement::Binding { key, binding, default } => {
                    let new_default = default.lower(scope)?;
                    let new_binding = binding.lower(scope)?;
                    retval.elements.push(low::MapBindingElement {
                        key: key,
                        binding: new_binding,
                        default: new_default,
                    });
                }
                MapBindingElement::SlurpTo(key) => {
                    if retval.slurp.is_some() {
                        return Err(Error::new(Syntax::MultiSlurp).tag(span, Action::Parse));
                    }
                    match scope.lookup_store(*key.as_ref()) {
                        None => return Err(Error::new(Reason::Unbound(*key.as_ref())).tag(key.span(), Action::LookupName)),
                        Some(index) => retval.slurp = Some(index),
                    }
                }
            }
        }

        Ok(retval)
    }
}

// Binding
// ----------------------------------------------------------------

/// A binding comes in three flavors: identifiers (which don't do any
/// destructuring), and list and map bindings, which destructures lists and maps
/// respectively.
#[derive(Debug, Clone, PartialEq)]
pub enum Binding {
    Identifier(Tagged<Key>),
    List(Tagged<ListBinding>),
    Map(Tagged<MapBinding>),
}

impl Binding {
    fn announce_bindings(&self, scope: &mut dyn SubScope) {
        match self {
            Self::Identifier(key) => { scope.announce_binding(*key.as_ref()); }
            Self::List(binding) => { binding.announce_bindings(scope); }
            Self::Map(binding) => { binding.announce_bindings(scope); }
        }
    }
}

impl Lower for Binding {
    type Target = low::Binding;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        match self {
            Self::Identifier(key) => match scope.lookup_store(*key.as_ref()) {
                None => Err(Error::new(Reason::Unbound(*key.as_ref())).tag(key.span(), Action::LookupName)),
                Some(index) => Ok(low::Binding::Slot(index)),
            }
            Self::List(binding) => Ok(low::Binding::List(binding.lower(scope)?)),
            Self::Map(binding) => Ok(low::Binding::Map(binding.lower(scope)?)),
        }
    }
}

// StringElement
// ----------------------------------------------------------------

/// A string element is anything that is legal in a string: either raw string
/// data or an interpolated expression. A string is represented as a li of
/// string elements.
#[derive(Debug, Clone, PartialEq)]
pub enum StringElement {
    Raw(Rc<String>),
    Interpolate(Tagged<Expr>, Option<FormatSpec>),
}

impl StringElement {
    /// Construct a raw string element.
    pub fn raw<T: AsRef<str>>(val: T) -> StringElement {
        StringElement::Raw(Rc::new(val.as_ref().to_owned()))
    }
}

impl Lower for StringElement {
    type Target = low::StringElement;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        match self {
            Self::Raw(str) => {
                let index = scope.new_constant(Object::new_str_natural(str.as_ref()));
                Ok(low::StringElement::Raw(index))
            }
            Self::Interpolate(expr, fmt) => Ok(low::StringElement::Interpolate(
                expr.lower(scope)?,
                fmt.map(|f| scope.new_fmt_spec(f)),
            )),
        }
    }
}

// ListElement
// ----------------------------------------------------------------

/// A list element is anything that is legal inside a list literal:
/// - singleton elements
/// - splatted expressions
/// - iterated elements
/// - conditional elements
#[derive(Debug, Clone, PartialEq)]
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

impl Lower for ListElement {
    type Target = low::ListElement;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        match self {
            Self::Singleton(expr) => Ok(low::ListElement::Singleton(expr.lower(scope)?)),
            Self::Splat(expr) => Ok(low::ListElement::Splat(expr.lower(scope)?)),
            Self::Cond { condition, element } => Ok(low::ListElement::Cond {
                condition: condition.lower(scope)?,
                element: Box::new(element.lower(scope)?),
            }),
            Self::Loop { binding, iterable, element } => {
                let mut subscope = LocalScope::new(scope);
                binding.announce_bindings(&mut subscope);

                let new_iterable = iterable.lower(&mut subscope)?;
                let new_binding = binding.lower(&mut subscope)?;
                let new_element = element.lower(&mut subscope)?;

                Ok(low::ListElement::Loop {
                    binding: new_binding,
                    slots: subscope.catalog(),
                    iterable: new_iterable,
                    element: Box::new(new_element),
                })
            }
        }
    }
}

// MapElement
// ----------------------------------------------------------------

/// A map element is anything that is legal in a map literal:
/// - singleton elements
/// - splatted expressions
/// - iterated elements
/// - conditional elements
#[derive(Debug, Clone, PartialEq)]
pub enum MapElement {
    Singleton {
        key: Tagged<Expr>,
        value: Tagged<Expr>,
    },
    Splat(Tagged<Expr>),
    Loop {
        binding: Tagged<Binding>,
        iterable: Tagged<Expr>,
        element: Box<Tagged<MapElement>>,
    },
    Cond {
        condition: Tagged<Expr>,
        element: Box<Tagged<MapElement>>,
    },
}

impl Lower for MapElement {
    type Target = low::MapElement;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        match self {
            Self::Singleton { key, value } => Ok(low::MapElement::Singleton {
                key: key.lower(scope)?,
                value: value.lower(scope)?,
            }),
            Self::Splat(expr) => Ok(low::MapElement::Splat(expr.lower(scope)?)),
            Self::Cond { condition, element } => Ok(low::MapElement::Cond {
                condition: condition.lower(scope)?,
                element: Box::new(element.lower(scope)?),
            }),
            Self::Loop { binding, iterable, element } => {
                let mut subscope = LocalScope::new(scope);
                binding.announce_bindings(&mut subscope);

                let new_iterable = iterable.lower(&mut subscope)?;
                let new_binding = binding.lower(&mut subscope)?;
                let new_element = element.lower(&mut subscope)?;

                Ok(low::MapElement::Loop {
                    binding: new_binding,
                    slots: subscope.catalog(),
                    iterable: new_iterable,
                    element: Box::new(new_element),
                })
            }
        }
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
#[derive(Debug, Clone, PartialEq)]
pub enum ArgElement {
    Singleton(Tagged<Expr>),
    Keyword(Tagged<Key>, Tagged<Expr>),
    Splat(Tagged<Expr>),
}

impl Lower for ArgElement {
    type Target = low::ArgElement;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        match self {
            Self::Singleton(expr) => Ok(low::ArgElement::Singleton(expr.lower(scope)?)),
            Self::Keyword(key, expr) => Ok(low::ArgElement::Keyword(key, expr.lower(scope)?)),
            Self::Splat(expr) => Ok(low::ArgElement::Splat(expr.lower(scope)?)),
        }
    }
}

// Operator
// ----------------------------------------------------------------

/// In Gold AST terms, a transform acts on a value and returns another. Thus,
/// all transform are of the form Expr -> Expr.
///
/// All unary and binary operators are realized as transforms. In an expression
/// such as x + y, the transform (+ y) acts on the 'operand' x.
#[derive(Debug, Clone, PartialEq)]
pub enum Transform {
    /// Unary operator
    UnOp(Tagged<Option<UnOp>>),

    /// Binary operator with right operand
    BinOp(Tagged<BinOp>, Box<Tagged<Expr>>),

    /// Function call operator with arguments
    FunCall(Tagged<Vec<Tagged<ArgElement>>>),
}

impl Transform {
    /// Construct an index/subscripting transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn index<U>(subscript: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Index).tag(loc), Box::new(subscript))
    }

    /// Construct an exponentiation transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn power<U>(exponent: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Power).tag(loc), Box::new(exponent))
    }

    /// Construct a multiplication transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn multiply<U>(multiplicand: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Multiply).tag(loc), Box::new(multiplicand))
    }

    /// Construct an integer division transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn integer_divide<U>(divisor: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::IntegerDivide).tag(loc), Box::new(divisor))
    }

    /// Construct a mathematical division transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn divide<U>(divisor: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Divide).tag(loc), Box::new(divisor))
    }

    /// Construct an addition transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn add<U>(addend: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Add).tag(loc), Box::new(addend))
    }

    /// Construct a subtraction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn subtract<U>(subtrahend: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Subtract).tag(loc), Box::new(subtrahend))
    }

    /// Construct a less-than transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn less<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Less).tag(loc), Box::new(rhs))
    }

    /// Construct a greater-than transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn greater<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Greater).tag(loc), Box::new(rhs))
    }

    /// Construct a less-than-or-equal transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn less_equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::LessEqual).tag(loc), Box::new(rhs))
    }

    /// Construct a greater-than-or-equal transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn greater_equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::GreaterEqual).tag(loc), Box::new(rhs))
    }

    /// Construct an equality check transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Equal).tag(loc), Box::new(rhs))
    }

    /// Construct an inequality check transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn not_equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::NotEqual).tag(loc), Box::new(rhs))
    }

    /// Construct a containment check transform.
    ///
    /// * `loc` - the location of the 'in' operator in the buffer.
    pub fn contains<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Eager(EagerOp::Contains).tag(loc), Box::new(rhs))
    }

    /// Construct a logical conjunction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn and<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Logic(LogicOp::And).tag(loc), Box::new(rhs))
    }

    /// Construct a logical disjunction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn or<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Logic(LogicOp::Or).tag(loc), Box::new(rhs))
    }
}

impl Lower for Transform {
    type Target = low::Transform;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        match self {
            Self::UnOp(op) => Ok(low::Transform::UnOp(op)),
            Self::BinOp(op, expr) => Ok(low::Transform::BinOp(op, Box::new(expr.lower(scope)?))),
            Self::FunCall(args) => {
                let (args, span) = args.decompose();
                let mut elements: Vec<Tagged<low::ArgElement>> = Vec::new();
                for arg in args {
                    elements.push(arg.lower(scope)?);
                }
                Ok(low::Transform::FunCall(elements.tag(span), true))
            }
        }
    }
}

// Expr
// ----------------------------------------------------------------

/// The most important AST node: an evaluatable expression.
#[derive(Debug, Clone, PartialEq)]
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
        /// Positional function parameters.
        positional: Tagged<ListBinding>,

        /// Optional keyword parameters.
        keywords: Option<Tagged<MapBinding>>,

        /// The expression to evaluate when called.
        expression: Box<Tagged<Expr>>,
    },

    /// A conditional branch. Gold doesn't have else-less branches.
    Branch {
        condition: Box<Tagged<Expr>>,
        true_branch: Box<Tagged<Expr>>,
        false_branch: Box<Tagged<Expr>>,
    },
}

impl Tagged<Expr> {
    /// Form a sum expression from two terms.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn add<U>(self, addend: Tagged<Expr>, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::add(addend, loc))
    }

    /// Form a subtraction expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn sub<U>(self, subtrahend: Tagged<Expr>, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::subtract(subtrahend, loc))
    }

    /// Form a multiplication expression from two factors.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn mul<U>(self, multiplicand: Tagged<Expr>, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::multiply(multiplicand, loc))
    }

    /// Form a division expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn div<U>(self, divisor: Tagged<Expr>, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::divide(divisor, loc))
    }

    /// Form an integer division expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn idiv<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::integer_divide(rhs, l))
    }

    /// Form a less-than expression from operandsterms.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn lt<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::less(rhs, l))
    }

    /// Form a greater-than expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn gt<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::greater(rhs, l))
    }

    /// Form a less-than-or-equal expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn lte<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::less_equal(rhs, l))
    }

    /// Form a greater-than-or-equal expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn gte<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::greater_equal(rhs, l))
    }

    /// Form an equality check expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn equal<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::equal(rhs, l))
    }

    /// Form an inequality check expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn not_equal<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::not_equal(rhs, l))
    }

    /// Form a logical conjunction expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn and<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::and(rhs, l))
    }

    /// Form a logical disjunction expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn or<U>(self, rhs: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::or(rhs, l))
    }

    /// Form an exponentiation expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn pow<U>(self, exponent: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::power(exponent, l))
    }

    /// Form a subscripting/indexing expression from two operands.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn index<U>(self, subscript: Tagged<Expr>, l: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::index(subscript, l))
    }

    /// Arithmetically negate this expression.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn neg<U>(self, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::UnOp(Some(UnOp::ArithmeticalNegate).tag(loc)))
    }

    /// Logically negate this expression.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn not<U>(self, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::UnOp(Some(UnOp::LogicalNegate).tag(loc)))
    }

    /// Form a function call expression from by calling this function with a
    /// list of arguments.
    ///
    /// * `loc` - the location of the function call operator in the buffer.
    pub fn funcall<U>(self, args: Vec<Tagged<ArgElement>>, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::FunCall(args.tag(loc)))
    }

    /// Form the combined transformed expression from this operand and a transform.
    fn transform(self, op: Transform) -> Expr {
        Expr::Transformed {
            operand: Box::new(self),
            transform: op,
        }
    }
}

impl Expr {
    /// Construct a string expression.
    ///
    /// If there's only one string element, and it's a raw string, (or if the
    /// string is empty) this will return a string literal.
    pub fn string(value: Vec<StringElement>) -> Expr {
        if value.len() == 0 {
            Expr::Literal(Object::from(""))
        } else if let [StringElement::Raw(val)] = &value[..] {
            Expr::Literal(Object::from(val.as_ref()))
        } else {
            Expr::String(value)
        }
    }
}

impl Lower for Expr {
    type Target = low::Expr;

    fn lower(self, scope: &mut dyn Scope) -> Res<Self::Target> {
        match self {
            Self::Literal(obj) => {
                let index = scope.new_constant(obj);
                Ok(low::Expr::Constant(index))
            }
            Self::String(elements) => {
                let mut new_elements = Vec::with_capacity(elements.len());
                for element in elements {
                    new_elements.push(element.lower(scope)?);
                }
                Ok(low::Expr::String(new_elements))
            }
            Self::Identifier(name) => {
                match scope.lookup_load(*name.as_ref(), false) {
                    None => {
                        match BUILTINS.0.get(name.as_str()) {
                            Some(index) => Ok(low::Expr::Builtin(*index)),
                            None => Err(Error::new(Reason::Unbound(*name.as_ref())).tag(name.span(), Action::LookupName)),
                        }
                    }
                    Some(slot) => Ok(low::Expr::Slot(slot)),
                }
            }
            Self::List(elements) => {
                let mut new_elements = Vec::new();
                for element in elements {
                    new_elements.push(element.lower(scope)?);
                }
                Ok(low::Expr::List(new_elements))
            }
            Self::Map(elements) => {
                let mut new_elements = Vec::new();
                for element in elements {
                    new_elements.push(element.lower(scope)?);
                }
                Ok(low::Expr::Map(new_elements))
            }
            Self::Let { bindings, expression } => {
                let mut builder = low::LetBuilder::new(scope);
                for (binding, _) in bindings.iter() {
                    binding.announce_bindings(builder.scope());
                }

                for (binding, expr) in bindings.into_iter() {
                    let new_expr = expr.lower(builder.scope())?;
                    let new_binding = binding.lower(builder.scope())?;
                    builder.add_binding(new_binding, new_expr);
                }

                let new_expression = expression.lower(builder.scope())?;
                builder.expression(new_expression);

                Ok(builder.finalize())
            }
            Self::Transformed { operand, transform } => {
                let operand = operand.lower(scope)?;
                let transform = transform.lower(scope)?;
                Ok(low::Expr::Transformed { operand: Box::new(operand), transform })
            }
            Self::Branch { condition, true_branch, false_branch } => {
                Ok(low::Expr::Branch {
                    condition: Box::new(condition.lower(scope)?),
                    true_branch: Box::new(true_branch.lower(scope)?),
                    false_branch: Box::new(false_branch.lower(scope)?),
                })
            }
            Self::Function { positional, keywords, expression } => {
                let mut builder = low::FunctionBuilder::new(Some(scope));

                positional.announce_bindings(builder.scope());
                if let Some(kw) = &keywords {
                    kw.announce_bindings(builder.scope());
                }

                let new_positional = positional.lower(builder.scope())?;
                let new_keywords = keywords.lower(builder.scope())?;
                let expr = expression.lower(builder.scope())?;

                builder.positional(new_positional);
                builder.keywords(new_keywords);
                builder.expression(expr);

                Ok(low::Expr::Func(builder.finalize()))
            }
        }
    }
}

// TopLevel
// ----------------------------------------------------------------

/// A top-level AST node, only legal at the top level of a file.
#[derive(Debug)]
pub enum TopLevel {
    /// Import an object by loading another file and binding it to a pattern.
    Import(Tagged<String>, Tagged<Binding>),
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

impl File {
    pub fn lower(self) -> Res<low::Function> {
        let mut outer = low::FunctionBuilder::new(None);

        let mut import_builder = low::ImportsBuilder::new(outer.scope());
        for statement in self.statements.iter() {
            let TopLevel::Import(_, binding) = statement;
            binding.announce_bindings(import_builder.scope());
        }
        for statement in self.statements.into_iter() {
            let TopLevel::Import(path, binding) = statement;
            let new_binding = binding.lower(import_builder.scope())?;
            import_builder.add_import(new_binding, path);
        }

        let mut inner_builder = low::FunctionBuilder::new(Some(import_builder.scope()));
        let expr = self.expression.lower(inner_builder.scope())?;
        inner_builder.expression(expr);
        let inner_expr = low::Expr::Func(inner_builder.finalize()).tag(0);

        import_builder.expression(inner_expr);
        let import_expr = import_builder.finalize().tag(0);

        let call_expr = low::Expr::Transformed {
            operand: Box::new(import_expr),
            transform: low::Transform::FunCall(vec![].tag(0), false),
        }.tag(0);
        outer.expression(call_expr);

        Ok(outer.finalize())
    }
}
