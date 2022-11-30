use std::collections::HashSet;
use std::sync::Arc;
use std::ops;

use serde::{Deserialize, Serialize};

use crate::error::BindingType;

use super::error::{Error, Tagged};
use super::object::{Object, Key};
use super::traits::{Boxable, Free, FreeImpl, FreeAndBound, Validatable, ToVec};


fn binding_element_free_and_bound<T: Free, U: FreeAndBound>(
    binding: &U,
    default: Option<&T>,
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ListBindingElement {
    Binding {
        binding: Tagged<Binding>,
        default: Option<Tagged<Expr>>,
    },
    SlurpTo(Tagged<Key>),
    Slurp,
}

impl Validatable for ListBindingElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ListBindingElement::Binding { binding, default } => {
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

impl FreeAndBound for ListBindingElement {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            ListBindingElement::Binding { binding, default } => {
                binding_element_free_and_bound(binding, default.as_ref(), free, bound);
            },
            ListBindingElement::SlurpTo(name) => { bound.insert(*name.as_ref()); },
            _ => {},
        }
    }
}


// MapBindingElement
// ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MapBindingElement {
    Binding {
        key: Tagged<Key>,
        binding: Tagged<Binding>,
        default: Option<Tagged<Expr>>,
    },
    SlurpTo(Tagged<Key>),
}

impl FreeAndBound for MapBindingElement {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            MapBindingElement::Binding { key: _, binding, default } => {
                binding_element_free_and_bound(binding, default.as_ref(), free, bound);
            },
            MapBindingElement::SlurpTo(name) => { bound.insert(*name.as_ref()); },
        }
    }
}

impl Validatable for MapBindingElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            MapBindingElement::Binding { binding, default, .. } => {
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ListBinding(pub Vec<Tagged<ListBindingElement>>);

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
            if let ListBindingElement::Binding { .. } = element.as_ref() { }
            else {
                if found_slurp {
                    return Err(Error::default())
                }
                found_slurp = true;
            }
        }
        Ok(())
    }
}


// MapBinding
// ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MapBinding(pub Vec<Tagged<MapBindingElement>>);

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
            if let MapBindingElement::SlurpTo(_) = element.as_ref() {
                if found_slurp {
                    return Err(Error::default())
                }
                found_slurp = true;
            }
        }
        Ok(())
    }
}


// Binding
// ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Binding {
    Identifier(Tagged<Key>),
    List(Tagged<ListBinding>),
    Map(Tagged<MapBinding>),
}

impl Binding {
    pub fn type_of(&self) -> BindingType {
        match self {
            Self::Identifier(_) => BindingType::Identifier,
            Self::List(_) => BindingType::List,
            Self::Map(_) => BindingType::Map,
        }
    }
}

impl FreeAndBound for Binding {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            Binding::Identifier(name) => { bound.insert(*name.as_ref()); },
            Binding::List(elements) => elements.free_and_bound(free, bound),
            Binding::Map(elements) => elements.free_and_bound(free, bound),
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum StringElement {
    Raw(Arc<str>),
    Interpolate(Tagged<Expr>),
}

impl StringElement {
    pub fn raw<T: AsRef<str>>(val: T) -> StringElement {
        StringElement::Raw(Arc::from(val.as_ref()))
    }
}

impl Validatable for StringElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            StringElement::Interpolate(node) => { node.as_ref().validate()?; }
            _ => {},
        }
        Ok(())
    }
}


// ListElement
// ----------------------------------------------------------------

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
            ListElement::Singleton(expr) => expr.as_ref().free_impl(free),
            ListElement::Splat(expr) => expr.as_ref().free_impl(free),
            ListElement::Cond { condition, element } => {
                condition.as_ref().free_impl(free);
                element.as_ref().as_ref().free_impl(free);
            },
            ListElement::Loop { binding, iterable, element } => {
                iterable.as_ref().free_impl(free);
                let mut bound: HashSet<Key> = HashSet::new();
                binding.as_ref().free_and_bound(free, &mut bound);
                for ident in element.as_ref().as_ref().free() {
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
            ListElement::Singleton(node) => { node.as_ref().validate()?; },
            ListElement::Splat(node) => { node.as_ref().validate()?; },
            ListElement::Loop { binding, iterable, element } => {
                binding.as_ref().validate()?;
                iterable.as_ref().validate()?;
                element.as_ref().as_ref().validate()?;
            },
            ListElement::Cond { condition, element } => {
                condition.as_ref().validate()?;
                element.as_ref().as_ref().validate()?;
            },
        }
        Ok(())
    }
}


// MapElement
// ----------------------------------------------------------------

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
                key.as_ref().free_impl(free);
                value.as_ref().free_impl(free);
            },
            MapElement::Splat(expr) => expr.as_ref().free_impl(free),
            MapElement::Cond { condition, element } => {
                condition.as_ref().free_impl(free);
                element.as_ref().as_ref().free_impl(free);
            },
            MapElement::Loop { binding, iterable, element } => {
                iterable.as_ref().free_impl(free);
                let mut bound: HashSet<Key> = HashSet::new();
                binding.as_ref().free_and_bound(free, &mut bound);
                for ident in element.as_ref().as_ref().free() {
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
                key.as_ref().validate()?;
                value.as_ref().validate()?;
            },
            MapElement::Splat(node) => { node.as_ref().validate()?; },
            MapElement::Loop { binding, iterable, element } => {
                binding.as_ref().validate()?;
                iterable.as_ref().validate()?;
                element.as_ref().as_ref().validate()?;
            },
            MapElement::Cond { condition, element } => {
                condition.as_ref().validate()?;
                element.as_ref().as_ref().validate()?;
            },
        }
        Ok(())
    }
}


// ArgElement
// ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ArgElement {
    Singleton(Tagged<Expr>),
    Keyword(Tagged<Key>, Tagged<Expr>),
    Splat(Tagged<Expr>),
}

impl FreeImpl for ArgElement {
    fn free_impl(&self, free: &mut HashSet<Key>) {
        match self {
            ArgElement::Singleton(expr) => { expr.as_ref().free_impl(free); },
            ArgElement::Splat(expr) => { expr.as_ref().free_impl(free); },
            ArgElement::Keyword(_, expr) => { expr.as_ref().free_impl(free); },
        }
    }
}

impl Validatable for ArgElement {
    fn validate(&self) -> Result<(), Error> {
        match self {
            ArgElement::Singleton(node) => { node.as_ref().validate()?; },
            ArgElement::Splat(node) => { node.as_ref().validate()?; },
            ArgElement::Keyword(_, value) => { value.as_ref().validate()?; },
        }
        Ok(())
    }
}


// Operator
// ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UnOp {
    Passthrough,
    ArithmeticalNegate,
    LogicalNegate,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum BinOp {
    Index,
    Power,
    Multiply,
    IntegerDivide,
    Divide,
    Add,
    Subtract,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Operator {
    UnOp(UnOp),
    BinOp(BinOp, Box<Tagged<Expr>>),
    FunCall(Vec<Tagged<ArgElement>>),
}

impl Operator {
    pub fn index<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Index, x.to_box()) }
    pub fn power<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Power, x.to_box()) }
    pub fn multiply<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Multiply, x.to_box()) }
    pub fn integer_divide<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::IntegerDivide, x.to_box()) }
    pub fn divide<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Divide, x.to_box()) }
    pub fn add<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Add, x.to_box()) }
    pub fn subtract<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Subtract, x.to_box()) }
    pub fn less<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Less, x.to_box()) }
    pub fn greater<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Greater, x.to_box()) }
    pub fn less_equal<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::LessEqual, x.to_box()) }
    pub fn greater_equal<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::GreaterEqual, x.to_box()) }
    pub fn equal<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Equal, x.to_box()) }
    pub fn not_equal<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::NotEqual, x.to_box()) }
    pub fn and<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::And, x.to_box()) }
    pub fn or<T>(x: T) -> Operator where T: Boxable<Tagged<Expr>> { Operator::BinOp(BinOp::Or, x.to_box()) }
}

impl Validatable for Operator {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Operator::BinOp(_, node) => { node.as_ref().as_ref().validate()?; },
            Operator::FunCall(args) => {
                for arg in args {
                    arg.as_ref().validate()?;
                }
            },
            _ => {},
        }
        Ok(())
    }
}


// Expr
// ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Literal(Object),
    String(Vec<StringElement>),
    Identifier(Tagged<Key>),
    List(Vec<Tagged<ListElement>>),
    Map(Vec<Tagged<MapElement>>),
    Let {
        bindings: Vec<(Tagged<Binding>, Tagged<Expr>)>,
        expression: Box<Tagged<Expr>>,
    },
    Operator {
        operand: Box<Tagged<Expr>>,
        operator: Operator,
    },
    Function {
        positional: ListBinding,
        keywords: Option<MapBinding>,
        expression: Box<Tagged<Expr>>,
    },
    Branch {
        condition: Box<Tagged<Expr>>,
        true_branch: Box<Tagged<Expr>>,
        false_branch: Box<Tagged<Expr>>,
    }
}

impl ops::Add<Tagged<Expr>> for Tagged<Expr> {
    type Output = Expr;
    fn add(self, rhs: Tagged<Expr>) -> Expr {
        self.operate(Operator::add(rhs))
    }
}

impl ops::Sub<Tagged<Expr>> for Tagged<Expr> {
    type Output = Expr;
    fn sub(self, rhs: Tagged<Expr>) -> Expr {
        self.operate(Operator::subtract(rhs))
    }
}

impl ops::Mul<Tagged<Expr>> for Tagged<Expr> {
    type Output = Expr;
    fn mul(self, rhs: Tagged<Expr>) -> Expr {
        self.operate(Operator::multiply(rhs))
    }
}

impl ops::Div<Tagged<Expr>> for Tagged<Expr> {
    type Output = Expr;
    fn div(self, rhs: Tagged<Expr>) -> Expr {
        self.operate(Operator::divide(rhs))
    }
}

impl ops::Neg for Tagged<Expr> {
    type Output = Expr;
    fn neg(self) -> Expr {
        self.operate(Operator::UnOp(UnOp::ArithmeticalNegate))
    }
}

impl ops::Not for Tagged<Expr> {
    type Output = Expr;
    fn not(self) -> Expr {
        self.operate(Operator::UnOp(UnOp::LogicalNegate))
    }
}

impl Tagged<Expr> {
    pub fn operate(self, op: Operator) -> Expr {
        Expr::Operator {
            operand: self.to_box(),
            operator: op,
        }
    }

    pub fn idiv(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::integer_divide(rhs)) }
    pub fn lt(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::less(rhs)) }
    pub fn gt(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::greater(rhs)) }
    pub fn lte(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::less_equal(rhs)) }
    pub fn gte(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::greater_equal(rhs)) }
    pub fn eql(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::equal(rhs)) }
    pub fn neql(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::not_equal(rhs)) }
    pub fn and(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::and(rhs)) }
    pub fn or(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::or(rhs)) }
    pub fn pow(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::power(rhs)) }
    pub fn index(self, rhs: Tagged<Expr>) -> Expr { self.operate(Operator::index(rhs)) }
    pub fn funcall<T>(self, args: T) -> Expr where T: ToVec<Tagged<ArgElement>> { self.operate(Operator::FunCall(args.to_vec())) }
}

impl Expr {
    pub fn list<T>(x: T) -> Expr where T: ToVec<Tagged<ListElement>> { Expr::List(x.to_vec()) }
    pub fn map<T>(x: T) -> Expr where T: ToVec<Tagged<MapElement>> { Expr::Map(x.to_vec()) }

    pub fn string(value: Vec<StringElement>) -> Expr {
        if value.len() == 0 {
            Expr::Literal(Object::int_string(""))
        } else if value.len() == 1 {
            match &value[0] {
                StringElement::Raw(val) if val.len() < 20 => Object::int_string(val.as_ref()).literal(),
                StringElement::Raw(val) => Object::nat_string(val).literal(),
                _ => Expr::String(value)
            }
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
            Expr::Identifier(name) => { free.insert(*name.as_ref()); },
            Expr::List(elements) => {
                for element in elements {
                    element.as_ref().free_impl(free);
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
                    binding.as_ref().free_and_bound(free, &mut bound);
                }
                for id in expression.free() {
                    if !bound.contains(&id) {
                        free.insert(id);
                    }
                }
            },
            Expr::Operator { operand, operator } => {
                operand.free_impl(free);
                match operator {
                    Operator::BinOp(_, expr) => expr.free_impl(free),
                    Operator::FunCall(elements) => {
                        for element in elements {
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
            Expr::Function { positional, keywords, expression } => {
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
                    element.as_ref().validate()?;
                }
            },
            Expr::Map(elements) => {
                for element in elements {
                    element.validate()?;
                }
            },
            Expr::Let { bindings, expression } => {
                for (binding, node) in bindings {
                    binding.as_ref().validate()?;
                    node.validate()?;
                }
                expression.validate()?;
            },
            Expr::Operator { operand, operator } => {
                operand.validate()?;
                operator.validate()?;
            },
            Expr::Function { positional, keywords, expression } => {
                positional.validate()?;
                keywords.as_ref().map(MapBinding::validate).transpose()?;
                expression.validate()?;
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

#[derive(Debug)]
pub enum TopLevel {
    Import(Tagged<String>, Tagged<Binding>),
}

impl Validatable for TopLevel {
    fn validate(&self) -> Result<(), Error> {
        match self {
            Self::Import(_, binding) => { binding.as_ref().validate()?; },
        }
        Ok(())
    }
}


// TopLevel
// ----------------------------------------------------------------


#[derive(Debug)]
pub struct File {
    pub statements: Vec<TopLevel>,
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
