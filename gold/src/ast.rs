use std::collections::{
    hash_map::{Iter, Keys},
    HashMap, HashSet,
};
use std::fmt::Display;

use gc::{Finalize, Gc, Trace};
use serde::{Deserialize, Serialize};

use crate::compile::{Compiler, Function};
use crate::error::{BindingType, Span, Syntax};
use crate::formatting::FormatSpec;

use crate::error::{Action, Error, Tagged, Taggable};
use crate::{Key, Object};

/// This trait is implemented by all AST nodes that require a validation step,
/// to catch integrity errors which the parser either can't or won't catch.
trait Validatable {
    /// Validate this node and return a suitable error if necessary.
    ///
    /// By the Anna Karenina rule, there's no distinction on success.
    fn validate(&self) -> Result<(), Error>;
}

impl<T: Validatable> Validatable for Tagged<T> {
    fn validate(&self) -> Result<(), Error> {
        self.as_ref().validate()
    }
}

pub(crate) trait Visitable {
    fn visit<T: Visitor>(&self, visitor: &mut T);
}

pub(crate) trait Visitor {
    fn free(&mut self, name: Key);
    fn bound(&mut self, name: Key);
    fn captured(&mut self, name: Key);
}

pub(crate) enum NameStatus {
    Free,
    Captured,
}

pub(crate) struct FreeNames {
    names: HashMap<Key, NameStatus>,
}

impl FreeNames {
    pub fn new() -> FreeNames {
        FreeNames {
            names: HashMap::new(),
        }
    }

    pub fn free_names<'a>(&'a self) -> Keys<'a, Key, NameStatus> {
        self.names.keys()
    }

    pub fn captured_names<'a>(&'a self) -> CapturedNamesIterator<'a> {
        CapturedNamesIterator {
            iter: self.names.iter(),
        }
    }
}

impl Visitor for FreeNames {
    fn free(&mut self, name: Key) {
        match self.names.get(&name) {
            Some(_) => {}
            None => {
                self.names.insert(name, NameStatus::Free);
            }
        }
    }

    fn captured(&mut self, name: Key) {
        self.names.insert(name, NameStatus::Captured);
    }

    fn bound(&mut self, _name: Key) {}
}

pub(crate) struct CapturedNamesIterator<'a> {
    iter: Iter<'a, Key, NameStatus>,
}

impl<'a> Iterator for CapturedNamesIterator<'a> {
    type Item = Key;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                Some((key, NameStatus::Captured)) => {
                    return Some(*key);
                }
                Some(_) => {}
                None => {
                    return None;
                }
            }
        }
    }
}

pub(crate) struct BindingShield<'a> {
    bound: HashSet<Key>,
    parent: &'a mut dyn Visitor,
}

impl<'a> BindingShield<'a> {
    pub fn new(parent: &'a mut dyn Visitor) -> BindingShield<'a> {
        BindingShield {
            bound: HashSet::new(),
            parent,
        }
    }
}

impl<'a> Visitor for BindingShield<'a> {
    fn free(&mut self, name: Key) {
        if !self.bound.contains(&name) {
            self.parent.free(name);
        }
    }

    fn captured(&mut self, name: Key) {
        if !self.bound.contains(&name) {
            self.parent.captured(name);
        }
    }

    fn bound(&mut self, name: Key) {
        self.bound.insert(name);
    }
}

pub(crate) struct FunctionThreshold<'a> {
    parent: &'a mut dyn Visitor,
}

impl<'a> FunctionThreshold<'a> {
    pub fn new(parent: &'a mut dyn Visitor) -> FunctionThreshold<'a> {
        FunctionThreshold { parent: parent }
    }
}

impl<'a> Visitor for FunctionThreshold<'a> {
    fn free(&mut self, name: Key) {
        self.parent.captured(name);
    }

    fn captured(&mut self, name: Key) {
        self.parent.captured(name);
    }

    fn bound(&mut self, _nmae: Key) {}
}

#[derive(PartialEq)]
pub(crate) enum BindingMode {
    Local,
    Cell,
}

pub(crate) struct BindingClassifier {
    bindings: HashMap<Key, BindingMode>,
}

impl BindingClassifier {
    pub fn new() -> BindingClassifier {
        BindingClassifier {
            bindings: HashMap::new(),
        }
    }

    pub fn names_with_mode(&self, mode: BindingMode) -> BindingClassifierIterator {
        BindingClassifierIterator {
            mode: mode,
            iter: self.bindings.iter(),
        }
    }
}

impl Visitor for BindingClassifier {
    fn free(&mut self, _name: Key) {}

    fn bound(&mut self, name: Key) {
        if !self.bindings.contains_key(&name) {
            self.bindings.insert(name, BindingMode::Local);
        }
    }

    fn captured(&mut self, name: Key) {
        self.bindings.insert(name, BindingMode::Cell);
    }
}

pub(crate) struct BindingClassifierIterator<'a> {
    mode: BindingMode,
    iter: Iter<'a, Key, BindingMode>,
}

impl<'a> Iterator for BindingClassifierIterator<'a> {
    type Item = Key;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                Some((key, mode)) if *mode == self.mode => {
                    return Some(*key);
                }
                None => {
                    return None;
                }
                Some(_) => {}
            }
        }
    }
}

// ListBindingElement
// ----------------------------------------------------------------

/// A list binding element is anything that is legal inside a list pattern.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub enum ListBindingElement {
    /// An ordinary binding with potential default value
    Binding {
        binding: Tagged<Binding>,
        default: Option<Tagged<Expr>>,
    },

    /// Slurp into a named list
    SlurpTo(#[unsafe_ignore_trace] Tagged<Key>),

    /// Slurp but discard values
    Slurp,
}

impl Visitable for ListBindingElement {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Binding { binding, default } => {
                if let Some(d) = default {
                    d.visit(visitor);
                }
                binding.visit(visitor);
            }
            Self::SlurpTo(name) => {
                visitor.bound(**name);
            }
            Self::Slurp => {}
        }
    }
}

impl Validatable for ListBindingElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ListBindingElement::Binding { binding, default } => {
                binding.validate()?;
                if let Some(node) = default {
                    node.validate()?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

// MapBindingElement
// ----------------------------------------------------------------

/// A map binding element is anything that is legan inside a map pattern.
///
/// Since map bindings discard superfluous values by default, there's no need
/// for an anonymous slurp.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub enum MapBindingElement {
    /// An ordinary binding with potential default value.
    Binding {
        #[unsafe_ignore_trace]
        key: Tagged<Key>,
        binding: Tagged<Binding>,
        default: Option<Tagged<Expr>>,
    },

    /// Slurp into a named map.
    SlurpTo(#[unsafe_ignore_trace] Tagged<Key>),
}

impl Visitable for MapBindingElement {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Binding {
                binding, default, ..
            } => {
                if let Some(d) = default {
                    d.visit(visitor);
                }
                binding.visit(visitor);
            }
            Self::SlurpTo(name) => {
                visitor.bound(**name);
            }
        }
    }
}

impl Validatable for MapBindingElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            MapBindingElement::Binding {
                binding, default, ..
            } => {
                binding.validate()?;
                if let Some(node) = default {
                    node.validate()?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

// ListBinding
// ----------------------------------------------------------------

/// A list binding destructures a list into a list of patterns.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub struct ListBinding(pub Vec<Tagged<ListBindingElement>>);

#[derive(Debug, Default)]
pub struct ListBindingSolution<'a> {
    pub num_front: usize,
    pub num_back: usize,
    pub def_front: usize,
    pub def_back: usize,
    pub slurp: Option<Option<Key>>,

    pub front: &'a [Tagged<ListBindingElement>],
    pub back: &'a [Tagged<ListBindingElement>],
}

impl<'a> ListBinding {
    pub fn solution(&'a self) -> ListBindingSolution<'a> {
        let mut ret = ListBindingSolution::default();

        for element in &self.0 {
            match element.as_ref() {
                ListBindingElement::Slurp => {
                    ret.slurp = Some(None);
                    continue;
                }
                ListBindingElement::SlurpTo(key) => {
                    ret.slurp = Some(Some(**key));
                    continue;
                }
                _ => {}
            }

            let has_default = if let ListBindingElement::Binding {
                default: Some(_), ..
            } = **element
            {
                true
            } else {
                false
            };
            match (has_default, ret.slurp) {
                (true, Some(_)) => ret.def_back += 1,
                (true, None) => ret.def_front += 1,
                (false, Some(_)) => ret.num_back += 1,
                (false, None) => ret.num_front += 1,
            }
        }

        ret.front = &self.0[..ret.num_front + ret.def_front];
        ret.back = &self.0[self.0.len() - ret.num_back - ret.def_back..];

        ret
    }
}

impl Visitable for ListBinding {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        for element in self.0.iter() {
            element.visit(visitor);
        }
    }
}

impl Validatable for ListBinding {
    fn validate(&self) -> Result<(), Error> {
        let mut found_slurp = false;
        let mut found_default = false;
        for element in &self.0 {
            element.validate()?;

            // It's illegal to have more than one slurp in a list binding.
            if let ListBindingElement::Binding { .. } = **element {
            } else {
                if found_slurp {
                    return Err(Error::new(Syntax::MultiSlurp).tag(element, Action::Parse));
                }
                found_slurp = true;
            }

            // It's illegal to have a non-default binding follow a default binding.
            if let ListBindingElement::Binding {
                default: Some(_), ..
            } = **element
            {
                found_default = true;
            } else if let ListBindingElement::Binding { default: None, .. } = **element {
                if found_default {
                    return Err(Error::new(Syntax::DefaultSequence).tag(element, Action::Parse));
                }
            }
        }
        Ok(())
    }
}

// MapBinding
// ----------------------------------------------------------------

/// A map binding destructres a map into a list of patterns associated with
/// keys.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub struct MapBinding(pub Vec<Tagged<MapBindingElement>>);

impl Visitable for MapBinding {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        for element in self.0.iter() {
            element.visit(visitor);
        }
    }
}

impl Validatable for MapBinding {
    fn validate<'a>(&'a self) -> Result<(), Error> {
        let mut found_slurp = false;
        for element in &self.0 {
            element.validate()?;

            // It's illegal to have more than one slurp in a map binding.
            if let MapBindingElement::SlurpTo(_) = **element {
                if found_slurp {
                    return Err(Error::new(Syntax::MultiSlurp).tag(element, Action::Parse));
                }
                found_slurp = true;
            }
        }
        Ok(())
    }
}

// Binding
// ----------------------------------------------------------------

/// A binding comes in three flavors: identifiers (which don't do any
/// destructuring), and list and map bindings, which destructures lists and maps
/// respectively.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub enum Binding {
    Identifier(#[unsafe_ignore_trace] Tagged<Key>),
    List(Tagged<ListBinding>),
    Map(Tagged<MapBinding>),
}

impl Binding {
    /// Return the type of the binding.
    pub fn type_of(&self) -> BindingType {
        match self {
            Self::Identifier(_) => BindingType::Identifier,
            Self::List(_) => BindingType::List,
            Self::Map(_) => BindingType::Map,
        }
    }
}

impl Visitable for Binding {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Identifier(name) => {
                visitor.bound(**name);
            }
            Self::List(binding) => {
                binding.visit(visitor);
            }
            Self::Map(binding) => {
                binding.visit(visitor);
            }
        }
    }
}

impl Validatable for Binding {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Binding::List(elements) => elements.validate(),
            Binding::Map(elements) => elements.validate(),
            _ => Ok(()),
        }
    }
}

// StringElement
// ----------------------------------------------------------------

/// A string element is anything that is legal in a string: either raw string
/// data or an interpolated expression. A string is represented as a li of
/// string elements.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub enum StringElement {
    Raw(Gc<String>),
    Interpolate(Tagged<Expr>, #[unsafe_ignore_trace] Option<FormatSpec>),
}

impl StringElement {
    /// Construct a raw string element.
    pub fn raw<T: AsRef<str>>(val: T) -> StringElement {
        StringElement::Raw(Gc::from(val.as_ref().to_owned()))
    }
}

impl Visitable for StringElement {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Interpolate(expr, _) => {
                expr.visit(visitor);
            }
            _ => {}
        }
    }
}

impl Validatable for StringElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            StringElement::Interpolate(node, _) => {
                node.validate()?;
            }
            _ => {}
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
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

impl Visitable for ListElement {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Singleton(expr) => {
                expr.visit(visitor);
            }
            Self::Splat(expr) => {
                expr.visit(visitor);
            }
            Self::Loop {
                binding,
                iterable,
                element,
            } => {
                iterable.visit(visitor);
                let mut shield = BindingShield::new(visitor);
                binding.visit(&mut shield);
                element.visit(&mut shield);
            }
            Self::Cond { condition, element } => {
                condition.visit(visitor);
                element.visit(visitor);
            }
        }
    }
}

impl Validatable for ListElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ListElement::Singleton(node) => {
                node.validate()?;
            }
            ListElement::Splat(node) => {
                node.validate()?;
            }
            ListElement::Loop {
                binding,
                iterable,
                element,
            } => {
                binding.validate()?;
                iterable.validate()?;
                element.validate()?;
            }
            ListElement::Cond { condition, element } => {
                condition.validate()?;
                element.validate()?;
            }
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
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

impl Visitable for MapElement {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Singleton { key, value } => {
                key.visit(visitor);
                value.visit(visitor);
            }
            Self::Splat(expr) => {
                expr.visit(visitor);
            }
            Self::Loop {
                binding,
                iterable,
                element,
            } => {
                iterable.visit(visitor);
                let mut shield = BindingShield::new(visitor);
                binding.visit(&mut shield);
                element.visit(&mut shield);
            }
            Self::Cond { condition, element } => {
                condition.visit(visitor);
                element.visit(visitor);
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
            }
            MapElement::Splat(node) => {
                node.validate()?;
            }
            MapElement::Loop {
                binding,
                iterable,
                element,
            } => {
                binding.validate()?;
                iterable.validate()?;
                element.validate()?;
            }
            MapElement::Cond { condition, element } => {
                condition.validate()?;
                element.validate()?;
            }
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub enum ArgElement {
    Singleton(Tagged<Expr>),
    Keyword(#[unsafe_ignore_trace] Tagged<Key>, Tagged<Expr>),
    Splat(Tagged<Expr>),
}

impl Visitable for ArgElement {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Singleton(expr) => {
                expr.visit(visitor);
            }
            Self::Keyword(_, expr) => {
                expr.visit(visitor);
            }
            Self::Splat(expr) => {
                expr.visit(visitor);
            }
        }
    }
}

impl Validatable for ArgElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ArgElement::Singleton(node) => {
                node.validate()?;
            }
            ArgElement::Splat(node) => {
                node.validate()?;
            }
            ArgElement::Keyword(_, value) => {
                value.validate()?;
            }
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

    /// Containment
    Contains,

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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub enum Transform {
    /// Unary operator
    UnOp(#[unsafe_ignore_trace] Tagged<UnOp>),

    /// Binary operator with right operand
    BinOp(#[unsafe_ignore_trace] Tagged<BinOp>, Box<Tagged<Expr>>),

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
        Transform::BinOp(BinOp::Index.tag(loc), Box::new(subscript))
    }

    /// Construct an exponentiation transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn power<U>(exponent: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Power.tag(loc), Box::new(exponent))
    }

    /// Construct a multiplication transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn multiply<U>(multiplicand: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Multiply.tag(loc), Box::new(multiplicand))
    }

    /// Construct an integer division transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn integer_divide<U>(divisor: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::IntegerDivide.tag(loc), Box::new(divisor))
    }

    /// Construct a mathematical division transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn divide<U>(divisor: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Divide.tag(loc), Box::new(divisor))
    }

    /// Construct an addition transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn add<U>(addend: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Add.tag(loc), Box::new(addend))
    }

    /// Construct a subtraction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn subtract<U>(subtrahend: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Subtract.tag(loc), Box::new(subtrahend))
    }

    /// Construct a less-than transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn less<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Less.tag(loc), Box::new(rhs))
    }

    /// Construct a greater-than transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn greater<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Greater.tag(loc), Box::new(rhs))
    }

    /// Construct a less-than-or-equal transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn less_equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::LessEqual.tag(loc), Box::new(rhs))
    }

    /// Construct a greater-than-or-equal transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn greater_equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::GreaterEqual.tag(loc), Box::new(rhs))
    }

    /// Construct an equality check transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Equal.tag(loc), Box::new(rhs))
    }

    /// Construct an inequality check transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn not_equal<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::NotEqual.tag(loc), Box::new(rhs))
    }

    /// Construct a containment check transform.
    ///
    /// * `loc` - the location of the 'in' operator in the buffer.
    pub fn contains<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Contains.tag(loc), Box::new(rhs))
    }

    /// Construct a logical conjunction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn and<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::And.tag(loc), Box::new(rhs))
    }

    /// Construct a logical disjunction transform.
    ///
    /// * `loc` - the location of the indexing operator in the buffer.
    pub fn or<U>(rhs: Tagged<Expr>, loc: U) -> Transform
    where
        Span: From<U>,
    {
        Transform::BinOp(BinOp::Or.tag(loc), Box::new(rhs))
    }
}

impl Visitable for Transform {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::BinOp(_, expr) => {
                expr.visit(visitor);
            }
            Self::FunCall(args) => {
                for arg in args.iter() {
                    arg.visit(visitor);
                }
            }
            Self::UnOp(_) => {}
        }
    }
}

impl Validatable for Transform {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Transform::BinOp(_, node) => {
                node.validate()?;
            }
            Transform::FunCall(args) => {
                for arg in args.as_ref() {
                    arg.validate()?;
                }
            }
            _ => {}
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
            Self::Contains => f.write_str("in"),
            Self::And => f.write_str("and"),
            Self::Or => f.write_str("or"),
        }
    }
}

// Expr
// ----------------------------------------------------------------

/// The most important AST node: an evaluatable expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace, Finalize)]
pub enum Expr {
    /// A literal object (usually numbers, booleans, null and strings).
    Literal(Object),

    /// A string as a vector of string elements (raw string data and
    /// interpolated expressions). During AST construction, a single raw string
    /// element is turned into a pure string literal.
    String(Vec<StringElement>),

    /// An identifier to be looked up by name.
    Identifier(#[unsafe_ignore_trace] Tagged<Key>),

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
        self.transform(Transform::UnOp(UnOp::ArithmeticalNegate.tag(loc)))
    }

    /// Logically negate this expression.
    ///
    /// * `loc` - the location of the operator in the buffer.
    pub fn not<U>(self, loc: U) -> Expr
    where
        Span: From<U>,
    {
        self.transform(Transform::UnOp(UnOp::LogicalNegate.tag(loc)))
    }

    /// Form the combined transformed expression from this operand and a transform.
    pub fn transform(self, op: Transform) -> Expr {
        Expr::Transformed {
            operand: Box::new(self),
            transform: op,
        }
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
}

impl Expr {
    /// Construct a list expression.
    pub fn list(elements: Vec<Tagged<ListElement>>) -> Expr where {
        Expr::List(elements)
    }

    /// Construct a map expression.
    pub fn map(x: Vec<Tagged<MapElement>>) -> Expr {
        Expr::Map(x)
    }

    /// Construct a string expression.
    ///
    /// If there's only one string element, and it's a raw string, (or if the
    /// string is empty) this will return a string literal.
    pub fn string(value: Vec<StringElement>) -> Expr {
        if value.len() == 0 {
            Expr::Literal(Object::new_str_interned(""))
        } else if let [StringElement::Raw(val)] = &value[..] {
            Expr::Literal(Object::new_str(val.as_ref()))
        } else {
            Expr::String(value)
        }
    }
}

impl Visitable for Expr {
    fn visit<T: Visitor>(&self, visitor: &mut T) {
        match self {
            Self::Literal(_) => {}
            Self::String(elements) => {
                for element in elements {
                    element.visit(visitor);
                }
            }
            Self::Identifier(name) => {
                visitor.free(**name);
            }
            Self::List(elements) => {
                for element in elements {
                    element.visit(visitor);
                }
            }
            Self::Map(elements) => {
                for element in elements {
                    element.visit(visitor);
                }
            }
            Self::Transformed { operand, transform } => {
                operand.visit(visitor);
                transform.visit(visitor);
            }
            Self::Branch {
                condition,
                true_branch,
                false_branch,
            } => {
                condition.visit(visitor);
                true_branch.visit(visitor);
                false_branch.visit(visitor);
            }
            Self::Let {
                bindings,
                expression,
            } => {
                let mut shield = BindingShield::new(visitor);
                for (binding, expr) in bindings {
                    expr.visit(&mut shield);
                    binding.visit(&mut shield);
                }
                expression.visit(&mut shield);
            }
            Self::Function {
                positional,
                keywords,
                expression,
            } => {
                let mut threshold = FunctionThreshold::new(visitor);
                let mut shield = BindingShield::new(&mut threshold);
                positional.visit(&mut shield);
                if let Some(kw) = keywords {
                    kw.visit(&mut shield);
                }
                expression.visit(&mut shield);
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
            }
            Expr::List(elements) => {
                for element in elements {
                    element.validate()?;
                }
            }
            Expr::Map(elements) => {
                for element in elements {
                    element.validate()?;
                }
            }
            Expr::Let {
                bindings,
                expression,
            } => {
                for (binding, node) in bindings {
                    binding.validate()?;
                    node.validate()?;
                }
                expression.validate()?;
            }
            Expr::Transformed {
                operand,
                transform: operator,
            } => {
                operand.validate()?;
                operator.validate()?;
            }
            Expr::Function {
                positional,
                keywords,
                expression,
            } => {
                positional.validate()?;
                keywords.as_ref().map(|b| b.validate()).transpose()?;
                expression.validate()?;
            }
            Expr::Branch {
                condition,
                true_branch,
                false_branch,
            } => {
                condition.validate()?;
                true_branch.validate()?;
                false_branch.validate()?;
            }
            _ => {}
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
    Import(Tagged<String>, Tagged<Binding>),
}

impl Validatable for TopLevel {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Self::Import(_, binding) => {
                binding.validate()?;
            }
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

impl File {
    pub fn validate(&self) -> Result<(), Error> {
        for statement in &self.statements {
            statement.validate()?;
        }
        self.expression.validate()?;
        Ok(())
    }
}

impl File {
    pub(crate) fn compile(&self) -> Result<Function, Error> {
        let mut compiler = Compiler::new();
        compiler.emit_file(self)?;
        Ok(compiler.finalize())
    }
}
