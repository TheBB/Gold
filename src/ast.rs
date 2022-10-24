use std::collections::HashSet;
use std::ops;
use std::rc::Rc;

use rug::Integer;

use super::object::{Object, ToObject};
use super::traits::{Boxable, Splat, Splattable};


#[derive(Debug, Clone, PartialEq)]
pub enum ListBindingElement {
    Binding {
        binding: Binding,
        default: Option<AstNode>,
    },
    SlurpTo(Rc<String>),
    Slurp,
}

impl ListBindingElement {
    pub fn slurp_to<T: ToString>(x: T) -> ListBindingElement { ListBindingElement::SlurpTo(Rc::new(x.to_string())) }
    pub fn free_and_bound(&self, free: &mut HashSet<Rc<String>>, bound: &mut HashSet<Rc<String>>) {
        match self {
            ListBindingElement::Binding { binding, default } => {
                binding_element_free_and_bound(binding, default, free, bound);
            },
            ListBindingElement::SlurpTo(name) => { bound.insert(name.clone()); },
            _ => {},
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum MapBindingElement {
    Binding {
        key: String,
        binding: Binding,
        default: Option<AstNode>,
    },
    SlurpTo(Rc<String>),
}

impl MapBindingElement {
    pub fn slurp_to<T: ToString>(x: T) -> MapBindingElement { MapBindingElement::SlurpTo(Rc::new(x.to_string())) }
    pub fn free_and_bound(&self, free: &mut HashSet<Rc<String>>, bound: &mut HashSet<Rc<String>>) {
        match self {
            MapBindingElement::Binding { key: _, binding, default } => {
                binding_element_free_and_bound(binding, default, free, bound);
            },
            MapBindingElement::SlurpTo(name) => { bound.insert(name.clone()); },
        }
    }
}

fn binding_element_free_and_bound(
    binding: &Binding,
    default: &Option<AstNode>,
    free: &mut HashSet<Rc<String>>,
    bound: &mut HashSet<Rc<String>>,
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

#[derive(Debug, Clone, PartialEq)]
pub enum Binding {
    Identifier(Rc<String>),
    List(Vec<ListBindingElement>),
    Map(Vec<MapBindingElement>),
}

impl Binding {
    pub fn id<T: ToString>(x: T) -> Binding { Binding::Identifier(Rc::new(x.to_string())) }

    pub fn free_and_bound(&self, free: &mut HashSet<Rc<String>>, bound: &mut HashSet<Rc<String>>) {
        match self {
            Binding::Identifier(name) => { bound.insert(name.clone()); },
            Binding::List(elements) => {
                for element in elements {
                    element.free_and_bound(free, bound);
                }
            },
            Binding::Map(elements) => {
                for element in elements {
                    element.free_and_bound(free, bound);
                }
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StringElement {
    Raw(Rc<String>),
    Interpolate(AstNode),
}

impl StringElement {
    pub fn raw<T>(val: T) -> StringElement where T: ToString {
        StringElement::Raw(Rc::new(val.to_string()))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ListElement {
    Singleton(AstNode),
    Splat(AstNode),
    Loop {
        binding: Binding,
        iterable: AstNode,
        element: Box<ListElement>,
    },
    Cond {
        condition: AstNode,
        element: Box<ListElement>,
    },
}

impl ListElement {
    pub fn free(&self) -> HashSet<Rc<String>> {
        let mut free: HashSet<Rc<String>> = HashSet::new();
        self.free_impl(&mut free);
        free
    }

    pub fn free_impl(&self, free: &mut HashSet<Rc<String>>) {
        match self {
            ListElement::Singleton(expr) => expr.free_impl(free),
            ListElement::Splat(expr) => expr.free_impl(free),
            ListElement::Cond { condition, element } => {
                condition.free_impl(free);
                element.free_impl(free);
            },
            ListElement::Loop { binding, iterable, element } => {
                iterable.free_impl(free);
                let mut bound: HashSet<Rc<String>> = HashSet::new();
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

pub trait ToListElement {
    fn to_list_element(self) -> ListElement;
}

impl ToListElement for ListElement {
    fn to_list_element(self) -> ListElement { self }
}

impl<T> ToListElement for T where T: ToAstNode {
    fn to_list_element(self) -> ListElement {
        ListElement::Singleton(self.to_ast())
    }
}

impl<T> ToListElement for Splat<T> where T: ToAstNode {
    fn to_list_element(self) -> ListElement {
        ListElement::Splat(self.object.to_ast())
    }
}

pub trait ToList {
    fn to_list(self) -> Vec<ListElement>;
}

impl ToList for Vec<ListElement> {
    fn to_list(self) -> Vec<ListElement> { self }
}

impl ToList for () {
    fn to_list(self) -> Vec<ListElement> { vec![] }
}

impl<A> ToList for (A,)
where
    A: ToListElement
{
    fn to_list(self) -> Vec<ListElement> {
        vec![self.0.to_list_element()]
    }
}

impl<A,B,> ToList for (A,B)
where
    A: ToListElement,
    B: ToListElement
{
    fn to_list(self) -> Vec<ListElement> {
        vec![
            self.0.to_list_element(),
            self.1.to_list_element(),
        ]
    }
}

impl<A,B,C> ToList for (A,B,C)
where
    A: ToListElement,
    B: ToListElement,
    C: ToListElement
{
    fn to_list(self) -> Vec<ListElement> {
        vec![
            self.0.to_list_element(),
            self.1.to_list_element(),
            self.2.to_list_element(),
        ]
    }
}

impl<A,B,C,D> ToList for (A,B,C,D)
where
    A: ToListElement,
    B: ToListElement,
    C: ToListElement,
    D: ToListElement
{
    fn to_list(self) -> Vec<ListElement> {
        vec![
            self.0.to_list_element(),
            self.1.to_list_element(),
            self.2.to_list_element(),
            self.3.to_list_element(),
        ]
    }
}

impl<A,B,C,D,E> ToList for (A,B,C,D,E)
where
    A: ToListElement,
    B: ToListElement,
    C: ToListElement,
    D: ToListElement,
    E: ToListElement
{
    fn to_list(self) -> Vec<ListElement> {
        vec![
            self.0.to_list_element(),
            self.1.to_list_element(),
            self.2.to_list_element(),
            self.3.to_list_element(),
            self.4.to_list_element(),
        ]
    }
}

impl Boxable<ListElement> for ListElement {
    fn to_box(self) -> Box<ListElement> { Box::new(self) }
}

impl ListElement {
    pub fn singleton<T>(x: T) -> ListElement where T: ToAstNode { ListElement::Singleton(x.to_ast()) }
    pub fn splat<T>(x: T) -> ListElement where T: ToAstNode { ListElement::Splat(x.to_ast()) }
}

#[derive(Debug, Clone, PartialEq)]
pub enum MapElement {
    Singleton {
        key: AstNode,
        value: AstNode,
    },
    Splat(AstNode),
    Loop {
        binding: Binding,
        iterable: AstNode,
        element: Box<MapElement>,
    },
    Cond {
        condition: AstNode,
        element: Box<MapElement>,
    },
}

impl MapElement {
    pub fn free(&self) -> HashSet<Rc<String>> {
        let mut free: HashSet<Rc<String>> = HashSet::new();
        self.free_impl(&mut free);
        free
    }

    pub fn free_impl(&self, free: &mut HashSet<Rc<String>>) {
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
                let mut bound: HashSet<Rc<String>> = HashSet::new();
                binding.free_and_bound(free, &mut bound);
                for ident in element.as_ref().free() {
                    if !bound.contains(&ident) {
                        free.insert(ident);
                    }
                }
            }
        }
    }
}


pub trait ToMapElement {
    fn to_map_element(self) -> MapElement;
}

impl ToMapElement for MapElement {
    fn to_map_element(self) -> MapElement { self }
}

impl<S,T> ToMapElement for (S, T) where T: ToAstNode, S: ToAstNode {
    fn to_map_element(self) -> MapElement {
        MapElement::Singleton {
            key: self.0.to_ast(),
            value: self.1.to_ast(),
        }
    }
}

impl<T> ToMapElement for Splat<T> where T: ToAstNode {
    fn to_map_element(self) -> MapElement {
        MapElement::Splat(self.object.to_ast())
    }
}

pub trait ToMap {
    fn to_map(self) -> Vec<MapElement>;
}

impl ToMap for Vec<MapElement> {
    fn to_map(self) -> Vec<MapElement> { self }
}

impl ToMap for () {
    fn to_map(self) -> Vec<MapElement> { vec![] }
}

impl<A> ToMap for (A,)
where
    A: ToMapElement
{
    fn to_map(self) -> Vec<MapElement> {
        vec![self.0.to_map_element()]
    }
}

impl<A,B> ToMap for (A,B)
where
    A: ToMapElement,
    B: ToMapElement
{
    fn to_map(self) -> Vec<MapElement> {
        vec![
            self.0.to_map_element(),
            self.1.to_map_element(),
        ]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ArgElement {
    Singleton(AstNode),
    Keyword(Rc<String>, AstNode),
    Splat(AstNode),
}

impl ArgElement {
    pub fn keyword<T>(key: T, val: AstNode) -> ArgElement where T: ToString {
        ArgElement::Keyword(Rc::new(key.to_string()), val)
    }

    pub fn free_impl(&self, free: &mut HashSet<Rc<String>>) {
        match self {
            ArgElement::Singleton(expr) => { expr.free_impl(free); },
            ArgElement::Splat(expr) => { expr.free_impl(free); },
            ArgElement::Keyword(_, expr) => { expr.free_impl(free); },
        }
    }
}

pub trait ToArg {
    fn to_arg(self) -> ArgElement;
}

impl<T> ToArg for T where T: ToAstNode {
    fn to_arg(self) -> ArgElement {
        ArgElement::Singleton(self.to_ast())
    }
}

impl<S,T> ToArg for (S, T) where S: ToString, T: ToAstNode {
    fn to_arg(self) -> ArgElement {
        ArgElement::Keyword(Rc::new(self.0.to_string()), self.1.to_ast())
    }
}

impl<T> ToArg for Splat<T> where T: ToAstNode {
    fn to_arg(self) -> ArgElement {
        ArgElement::Splat(self.object.to_ast())
    }
}

pub trait ToArgs {
    fn to_args(self) -> Vec<ArgElement>;
}

impl ToArgs for Vec<ArgElement> {
    fn to_args(self) -> Vec<ArgElement> { self }
}

impl ToArgs for () {
    fn to_args(self) -> Vec<ArgElement> { vec![] }
}

impl<A> ToArgs for (A,) where A: ToArg {
    fn to_args(self) -> Vec<ArgElement> {
        vec![self.0.to_arg()]
    }
}

impl<A,B> ToArgs for (A,B)
where
    A: ToArg,
    B: ToArg
{
    fn to_args(self) -> Vec<ArgElement> {
        vec![
            self.0.to_arg(),
            self.1.to_arg(),
        ]
    }
}

impl<A,B,C> ToArgs for (A,B,C)
where
    A: ToArg,
    B: ToArg,
    C: ToArg
{
    fn to_args(self) -> Vec<ArgElement> {
        vec![
            self.0.to_arg(),
            self.1.to_arg(),
            self.2.to_arg(),
        ]
    }
}

impl<A,B,C,D> ToArgs for (A,B,C,D)
where
    A: ToArg,
    B: ToArg,
    C: ToArg,
    D: ToArg
{
    fn to_args(self) -> Vec<ArgElement> {
        vec![
            self.0.to_arg(),
            self.1.to_arg(),
            self.2.to_arg(),
            self.3.to_arg(),
        ]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnOp {
    ArithmeticalNegate,
    LogicalNegate,
}

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub enum Operator {
    UnOp(UnOp),
    BinOp(BinOp, Box<AstNode>),
    FunCall(Vec<ArgElement>),
}

impl Operator {
    pub fn index<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Index, x.to_box()) }
    pub fn power<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Power, x.to_box()) }
    pub fn multiply<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Multiply, x.to_box()) }
    pub fn integer_divide<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::IntegerDivide, x.to_box()) }
    pub fn divide<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Divide, x.to_box()) }
    pub fn add<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Add, x.to_box()) }
    pub fn subtract<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Subtract, x.to_box()) }
    pub fn less<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Less, x.to_box()) }
    pub fn greater<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Greater, x.to_box()) }
    pub fn less_equal<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::LessEqual, x.to_box()) }
    pub fn greater_equal<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::GreaterEqual, x.to_box()) }
    pub fn equal<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Equal, x.to_box()) }
    pub fn not_equal<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::NotEqual, x.to_box()) }
    pub fn and<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::And, x.to_box()) }
    pub fn or<T>(x: T) -> Operator where T: Boxable<AstNode> { Operator::BinOp(BinOp::Or, x.to_box()) }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    Literal(Object),
    String(Vec<StringElement>),
    Identifier(Rc<String>),
    List(Vec<ListElement>),
    Map(Vec<MapElement>),
    Let {
        bindings: Vec<(Binding, AstNode)>,
        expression: Box<AstNode>,
    },
    Operator {
        operand: Box<AstNode>,
        operator: Operator,
    },
    Function {
        positional: Binding,
        keywords: Binding,
        expression: Box<AstNode>,
    },
    Branch {
        condition: Box<AstNode>,
        true_branch: Box<AstNode>,
        false_branch: Box<AstNode>,
    }
}

impl Boxable<AstNode> for AstNode {
    fn to_box(self) -> Box<AstNode> { Box::new(self) }
}

impl Splattable<AstNode> for AstNode {
    fn splat(self) -> Splat<AstNode> { Splat::<AstNode> { object: self } }
}

impl<T> ops::Add<T> for AstNode where T: ToAstNode {
    type Output = AstNode;
    fn add(self, rhs: T) -> AstNode { self.operate(Operator::add(rhs.to_ast())) }
}

impl<T> ops::Sub<T> for AstNode where T: ToAstNode {
    type Output = AstNode;
    fn sub(self, rhs: T) -> AstNode { self.operate(Operator::subtract(rhs.to_ast())) }
}

impl<T> ops::Mul<T> for AstNode where T: ToAstNode {
    type Output = AstNode;
    fn mul(self, rhs: T) -> AstNode { self.operate(Operator::multiply(rhs.to_ast())) }
}

impl<T> ops::Div<T> for AstNode where T: ToAstNode {
    type Output = AstNode;
    fn div(self, rhs: T) -> AstNode { self.operate(Operator::divide(rhs.to_ast())) }
}

impl ops::Neg for AstNode {
    type Output = AstNode;
    fn neg(self) -> AstNode { self.operate(Operator::UnOp(UnOp::ArithmeticalNegate)) }
}

impl ops::Not for AstNode {
    type Output = AstNode;
    fn not(self) -> AstNode { self.operate(Operator::UnOp(UnOp::LogicalNegate)) }
}

impl AstNode {
    pub fn integer(value: i64) -> AstNode { AstNode::Literal(Object::Integer(value)) }
    pub fn big_integer(value: Integer) -> AstNode { AstNode::Literal(Object::from(value)) }
    pub fn float(value: f64) -> AstNode { AstNode::Literal(Object::Float(value)) }
    pub fn boolean(value: bool) -> AstNode { AstNode::Literal(Object::Boolean(value)) }
    pub fn null() -> AstNode { AstNode::Literal(Object::Null) }

    pub fn id<T: ToString>(x: T) -> AstNode { AstNode::Identifier(Rc::new(x.to_string())) }

    pub fn list<T>(x: T) -> AstNode where T: ToList { AstNode::List(x.to_list()) }
    pub fn map<T>(x: T) -> AstNode where T: ToMap { AstNode::Map(x.to_map()) }

    pub fn operate(self, op: Operator) -> AstNode {
        AstNode::Operator {
            operand: self.to_box(),
            operator: op,
        }
    }

    pub fn idiv<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::integer_divide(rhs.to_ast())) }
    pub fn lt<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::less(rhs.to_ast())) }
    pub fn gt<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::greater(rhs.to_ast())) }
    pub fn lte<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::less_equal(rhs.to_ast())) }
    pub fn gte<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::greater_equal(rhs.to_ast())) }
    pub fn eql<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::equal(rhs.to_ast())) }
    pub fn neql<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::not_equal(rhs.to_ast())) }
    pub fn and<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::and(rhs.to_ast())) }
    pub fn or<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::or(rhs.to_ast())) }
    pub fn pow<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::power(rhs.to_ast())) }
    pub fn index<T>(self, rhs: T) -> AstNode where T: ToAstNode { self.operate(Operator::index(rhs.to_ast())) }
    pub fn funcall<T>(self, args: T) -> AstNode where T: ToArgs { self.operate(Operator::FunCall(args.to_args())) }

    pub fn string(value: Vec<StringElement>) -> AstNode {
        if value.len() == 0 {
            AstNode::Literal(Object::String(Rc::new("".to_string())))
        } else if value.len() == 1 {
            match &value[0] {
                StringElement::Raw(val) => AstNode::Literal(Object::String(val.clone())),
                _ => AstNode::String(value)
            }
        } else {
            AstNode::String(value)
        }
    }

    pub fn free(&self) -> HashSet<Rc<String>> {
        let mut free: HashSet<Rc<String>> = HashSet::new();
        self.free_impl(&mut free);
        free
    }

    pub fn free_impl(&self, free: &mut HashSet<Rc<String>>) {
        match self {
            AstNode::Literal(_) => {},
            AstNode::String(elements) => {
                for element in elements {
                    if let StringElement::Interpolate(expr) = element {
                        expr.free_impl(free);
                    }
                }
            },
            AstNode::Identifier(name) => { free.insert(name.clone()); },
            AstNode::List(elements) => {
                for element in elements {
                    element.free_impl(free);
                }
            },
            AstNode::Map(elements) => {
                for element in elements {
                    element.free_impl(free);
                }
            },
            AstNode::Let { bindings, expression } => {
                let mut bound: HashSet<Rc<String>> = HashSet::new();
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
            AstNode::Operator { operand, operator } => {
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
            AstNode::Branch { condition, true_branch, false_branch } => {
                condition.free_impl(free);
                true_branch.free_impl(free);
                false_branch.free_impl(free);
            },
            AstNode::Function { positional, keywords, expression } => {
                let mut bound: HashSet<Rc<String>> = HashSet::new();
                positional.free_and_bound(free, &mut bound);
                keywords.free_and_bound(free, &mut bound);
                for id in expression.free() {
                    if !bound.contains(&id) {
                        free.insert(id);
                    }
                }
            }
        }
    }
}

pub trait ToAstNode {
    fn to_ast(self) -> AstNode;
}

impl<T> ToAstNode for T where T: ToObject {
    fn to_ast(self) -> AstNode { self.to_object().literal() }
}

impl ToAstNode for AstNode {
    fn to_ast(self) -> AstNode { self }
}

pub trait IdAble {
    fn id(self) -> AstNode;
}

impl<T> IdAble for T where T: ToString {
    fn id(self) -> AstNode { AstNode::id(self.to_string()) }
}
