use std::collections::HashSet;
use std::sync::Arc;
use std::ops;

use num_bigint::BigInt;

use serde::{Deserialize, Serialize};

use super::object::{Object, Key};
use super::traits::{Boxable, Splat, Splattable, ToVec};


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ListBindingElement {
    Binding {
        binding: Binding,
        default: Option<Expr>,
    },
    SlurpTo(Key),
    Slurp,
}

impl ListBindingElement {
    pub fn slurp_to<T: ToString>(x: T) -> ListBindingElement { ListBindingElement::SlurpTo(Key::new(x.to_string())) }

    pub fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            ListBindingElement::Binding { binding, default } => {
                binding_element_free_and_bound(binding, default, free, bound);
            },
            ListBindingElement::SlurpTo(name) => { bound.insert(name.clone()); },
            _ => {},
        }
    }

    pub fn validate(&self) -> Result<(), String> {
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MapBindingElement {
    Binding {
        key: Key,
        binding: Binding,
        default: Option<Expr>,
    },
    SlurpTo(Key),
}

impl MapBindingElement {
    pub fn slurp_to<T: ToString>(x: T) -> MapBindingElement { MapBindingElement::SlurpTo(Key::new(x.to_string())) }

    pub fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            MapBindingElement::Binding { key: _, binding, default } => {
                binding_element_free_and_bound(binding, default, free, bound);
            },
            MapBindingElement::SlurpTo(name) => { bound.insert(name.clone()); },
        }
    }

    pub fn validate(&self) -> Result<(), String> {
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


fn binding_element_free_and_bound(
    binding: &Binding,
    default: &Option<Expr>,
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


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ListBinding(pub Vec<ListBindingElement>);

impl ListBinding {
    pub fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        for element in &self.0 {
            element.free_and_bound(free, bound);
        }
    }

    pub fn validate(&self) -> Result<(), String> {
        let mut found_slurp = false;
        for element in &self.0 {
            element.validate()?;
            if let ListBindingElement::Binding { .. } = element { }
            else {
                if found_slurp {
                    return Err("multiple slurps in list binding".to_string())
                }
                found_slurp = true;
            }
        }
        Ok(())
    }
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MapBinding(pub Vec<MapBindingElement>);

impl MapBinding {
    pub fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        for element in &self.0 {
            element.free_and_bound(free, bound);
        }
    }

    pub fn validate<'a>(&'a self) -> Result<(), String> {
        let mut found_slurp = false;
        for element in &self.0 {
            element.validate()?;
            if let MapBindingElement::SlurpTo(_) = element {
                if found_slurp {
                    return Err("multiple slurps in map binding".to_string())
                }
                found_slurp = true;
            }
        }
        Ok(())
    }
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Binding {
    Identifier(Key),
    List(ListBinding),
    Map(MapBinding),
}

impl Binding {
    pub fn id<T: ToString>(x: T) -> Binding { Binding::Identifier(Key::new(x.to_string())) }

    pub fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        match self {
            Binding::Identifier(name) => { bound.insert(name.clone()); },
            Binding::List(elements) => elements.free_and_bound(free, bound),
            Binding::Map(elements) => elements.free_and_bound(free, bound),
        }
    }

    pub fn validate(&self) -> Result<(), String> {
        match self {
            Binding::List(elements) => elements.validate(),
            Binding::Map(elements) => elements.validate(),
            _ => Ok(()),
        }
    }
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum StringElement {
    Raw(Arc<str>),
    Interpolate(Expr),
}

impl StringElement {
    pub fn raw<T: AsRef<str>>(val: T) -> StringElement {
        StringElement::Raw(Arc::from(val.as_ref()))
    }

    pub fn validate(&self) -> Result<(), String> {
        match self {
            StringElement::Interpolate(node) => { node.validate()?; }
            _ => {},
        }
        Ok(())
    }
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ListElement {
    Singleton(Expr),
    Splat(Expr),
    Loop {
        binding: Binding,
        iterable: Expr,
        element: Box<ListElement>,
    },
    Cond {
        condition: Expr,
        element: Box<ListElement>,
    },
}

impl ListElement {
    pub fn free(&self) -> HashSet<Key> {
        let mut free: HashSet<Key> = HashSet::new();
        self.free_impl(&mut free);
        free
    }

    pub fn free_impl(&self, free: &mut HashSet<Key>) {
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

    pub fn singleton<T>(x: T) -> ListElement where T: ToAstNode { ListElement::Singleton(x.to_ast()) }
    pub fn splat<T>(x: T) -> ListElement where T: ToAstNode { ListElement::Splat(x.to_ast()) }

    pub fn validate(&self) -> Result<(), String> {
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

impl<T> From<T> for ListElement where T: ToAstNode {
    fn from(x: T) -> ListElement {
        ListElement::Singleton(x.to_ast())
    }
}

impl<T> From<Splat<T>> for ListElement where T: ToAstNode {
    fn from(x: Splat<T>) -> ListElement {
        ListElement::Splat(x.object.to_ast())
    }
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MapElement {
    Singleton {
        key: Expr,
        value: Expr,
    },
    Splat(Expr),
    Loop {
        binding: Binding,
        iterable: Expr,
        element: Box<MapElement>,
    },
    Cond {
        condition: Expr,
        element: Box<MapElement>,
    },
}

impl MapElement {
    pub fn free(&self) -> HashSet<Key> {
        let mut free: HashSet<Key> = HashSet::new();
        self.free_impl(&mut free);
        free
    }

    pub fn free_impl(&self, free: &mut HashSet<Key>) {
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
                for ident in element.as_ref().free() {
                    if !bound.contains(&ident) {
                        free.insert(ident);
                    }
                }
            }
        }
    }

    pub fn validate(&self) -> Result<(), String> {
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


impl<S,T> From<(S,T)> for MapElement where T: ToAstNode, S: ToAstNode {
    fn from(x: (S,T)) -> Self {
        MapElement::Singleton { key: x.0.to_ast(), value: x.1.to_ast() }
    }
}

impl<T> From<Splat<T>> for MapElement where T: ToAstNode {
    fn from(x: Splat<T>) -> Self {
        MapElement::Splat(x.object.to_ast())
    }
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ArgElement {
    Singleton(Expr),
    Keyword(Key, Expr),
    Splat(Expr),
}

impl ArgElement {
    pub fn keyword<T>(key: T, val: Expr) -> ArgElement where T: ToString {
        ArgElement::Keyword(Key::new(key.to_string()), val)
    }

    pub fn free_impl(&self, free: &mut HashSet<Key>) {
        match self {
            ArgElement::Singleton(expr) => { expr.free_impl(free); },
            ArgElement::Splat(expr) => { expr.free_impl(free); },
            ArgElement::Keyword(_, expr) => { expr.free_impl(free); },
        }
    }

    pub fn validate(&self) -> Result<(), String> {
        match self {
            ArgElement::Singleton(node) => { node.validate()?; },
            ArgElement::Splat(node) => { node.validate()?; },
            ArgElement::Keyword(_, value) => { value.validate()?; },
        }
        Ok(())
    }
}

impl<T> From<T> for ArgElement where T: ToAstNode {
    fn from(x: T) -> Self {
        ArgElement::Singleton(x.to_ast())
    }
}

impl<S,T> From<(S,T)> for ArgElement where S: ToString, T: ToAstNode {
    fn from(x: (S,T)) -> Self {
        ArgElement::Keyword(Key::new(x.0.to_string()), x.1.to_ast())
    }
}

impl<T> From<Splat<T>> for ArgElement where T: ToAstNode {
    fn from(x: Splat<T>) -> Self {
        ArgElement::Splat(x.object.to_ast())
    }
}


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
    BinOp(BinOp, Box<Expr>),
    FunCall(Vec<ArgElement>),
}

impl Operator {
    pub fn index<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Index, x.to_box()) }
    pub fn power<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Power, x.to_box()) }
    pub fn multiply<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Multiply, x.to_box()) }
    pub fn integer_divide<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::IntegerDivide, x.to_box()) }
    pub fn divide<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Divide, x.to_box()) }
    pub fn add<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Add, x.to_box()) }
    pub fn subtract<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Subtract, x.to_box()) }
    pub fn less<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Less, x.to_box()) }
    pub fn greater<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Greater, x.to_box()) }
    pub fn less_equal<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::LessEqual, x.to_box()) }
    pub fn greater_equal<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::GreaterEqual, x.to_box()) }
    pub fn equal<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Equal, x.to_box()) }
    pub fn not_equal<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::NotEqual, x.to_box()) }
    pub fn and<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::And, x.to_box()) }
    pub fn or<T>(x: T) -> Operator where T: Boxable<Expr> { Operator::BinOp(BinOp::Or, x.to_box()) }

    pub fn validate(&self) -> Result<(), String> {
        match self {
            Operator::BinOp(_, node) => { node.validate()?; },
            Operator::FunCall(args) => {
                for arg in args {
                    arg.validate()?;
                }
            },
            _ => {},
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Literal(Object),
    String(Vec<StringElement>),
    Identifier(Key),
    List(Vec<ListElement>),
    Map(Vec<MapElement>),
    Let {
        bindings: Vec<(Binding, Expr)>,
        expression: Box<Expr>,
    },
    Operator {
        operand: Box<Expr>,
        operator: Operator,
    },
    Function {
        positional: ListBinding,
        keywords: Option<MapBinding>,
        expression: Box<Expr>,
    },
    Branch {
        condition: Box<Expr>,
        true_branch: Box<Expr>,
        false_branch: Box<Expr>,
    }
}

impl Splattable<Expr> for Expr {
    fn splat(&self) -> Splat<Expr> { Splat::<Expr> { object: self.clone() } }
}

impl<T> ops::Add<T> for Expr where T: ToAstNode {
    type Output = Expr;
    fn add(self, rhs: T) -> Expr { self.operate(Operator::add(rhs.to_ast())) }
}

impl<T> ops::Sub<T> for Expr where T: ToAstNode {
    type Output = Expr;
    fn sub(self, rhs: T) -> Expr { self.operate(Operator::subtract(rhs.to_ast())) }
}

impl<T> ops::Mul<T> for Expr where T: ToAstNode {
    type Output = Expr;
    fn mul(self, rhs: T) -> Expr { self.operate(Operator::multiply(rhs.to_ast())) }
}

impl<T> ops::Div<T> for Expr where T: ToAstNode {
    type Output = Expr;
    fn div(self, rhs: T) -> Expr { self.operate(Operator::divide(rhs.to_ast())) }
}

impl ops::Neg for Expr {
    type Output = Expr;
    fn neg(self) -> Expr { self.operate(Operator::UnOp(UnOp::ArithmeticalNegate)) }
}

impl ops::Not for Expr {
    type Output = Expr;
    fn not(self) -> Expr { self.operate(Operator::UnOp(UnOp::LogicalNegate)) }
}

impl Expr {
    pub fn integer(value: i64) -> Expr { Expr::Literal(Object::Integer(value)) }
    pub fn big_integer(value: BigInt) -> Expr { Expr::Literal(Object::from(value)) }
    pub fn float(value: f64) -> Expr { Expr::Literal(Object::Float(value)) }
    pub fn boolean(value: bool) -> Expr { Expr::Literal(Object::Boolean(value)) }
    pub fn null() -> Expr { Expr::Literal(Object::Null) }

    pub fn id<T: AsRef<str>>(x: T) -> Expr { Expr::Identifier(Key::new(x)) }

    pub fn list<T>(x: T) -> Expr where T: ToVec<ListElement> { Expr::List(x.to_vec()) }
    pub fn map<T>(x: T) -> Expr where T: ToVec<MapElement> { Expr::Map(x.to_vec()) }

    pub fn operate(self, op: Operator) -> Expr {
        Expr::Operator {
            operand: self.to_box(),
            operator: op,
        }
    }

    pub fn idiv<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::integer_divide(rhs.to_ast())) }
    pub fn lt<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::less(rhs.to_ast())) }
    pub fn gt<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::greater(rhs.to_ast())) }
    pub fn lte<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::less_equal(rhs.to_ast())) }
    pub fn gte<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::greater_equal(rhs.to_ast())) }
    pub fn eql<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::equal(rhs.to_ast())) }
    pub fn neql<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::not_equal(rhs.to_ast())) }
    pub fn and<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::and(rhs.to_ast())) }
    pub fn or<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::or(rhs.to_ast())) }
    pub fn pow<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::power(rhs.to_ast())) }
    pub fn index<T>(self, rhs: T) -> Expr where T: ToAstNode { self.operate(Operator::index(rhs.to_ast())) }
    pub fn funcall<T>(self, args: T) -> Expr where T: ToVec<ArgElement> { self.operate(Operator::FunCall(args.to_vec())) }

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

    pub fn free(&self) -> HashSet<Key> {
        let mut free: HashSet<Key> = HashSet::new();
        self.free_impl(&mut free);
        free
    }

    pub fn free_impl(&self, free: &mut HashSet<Key>) {
        match self {
            Expr::Literal(_) => {},
            Expr::String(elements) => {
                for element in elements {
                    if let StringElement::Interpolate(expr) = element {
                        expr.free_impl(free);
                    }
                }
            },
            Expr::Identifier(name) => { free.insert(name.clone()); },
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

    pub fn validate(&self) -> Result<(), String> {
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


pub trait ToAstNode {
    fn to_ast(self) -> Expr;
}

impl<T> ToAstNode for T where Expr: From<T> {
    fn to_ast(self) -> Expr {
        Expr::from(self)
    }
}

impl<T> From<T> for Expr where Object: From<T> {
    fn from(x: T) -> Self {
        Object::from(x).literal()
    }
}

pub trait IdAble {
    fn id(self) -> Expr;
}

impl<T> IdAble for T where T: AsRef<str> {
    fn id(self) -> Expr { Expr::id(self) }
}


#[derive(Debug)]
pub enum TopLevel {
    Import(String, Binding),
}

impl TopLevel {
    pub fn validate(&self) -> Result<(), String> {
        match self {
            Self::Import(_, binding) => { binding.validate()?; },
        }
        Ok(())
    }
}


#[derive(Debug)]
pub struct File {
    pub statements: Vec<TopLevel>,
    pub expression: Expr,
}

impl File {
    pub fn validate(&self) -> Result<(), String> {
        for statement in &self.statements {
            statement.validate()?;
        }
        self.expression.validate()?;
        Ok(())
    }
}
