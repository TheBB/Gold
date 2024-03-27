use crate::compile::{Compiler, CompiledFunction};
use crate::error::Tagged;
use crate::formatting::FormatSpec;
use crate::{Error, Object};
use crate::types::{UnOp, BinOp, Key};
use super::scope::{BindingLoc, ClosureScope, LocalScope, Scope, SlotCatalog};

#[derive(Debug, Clone)]
pub enum Binding {
    Slot(usize),
    List(Tagged<ListBinding>),
    Map(Tagged<MapBinding>),
}

#[derive(Debug, Default, Clone)]
pub struct ListBinding {
    pub num_front: usize,
    pub num_back: usize,
    pub def_front: usize,
    pub def_back: usize,
    pub slurp: Option<Option<usize>>,

    pub front: Vec<(Tagged<Binding>, Option<Tagged<Expr>>)>,
    pub back: Vec<(Tagged<Binding>, Option<Tagged<Expr>>)>,
}

impl ListBinding {
    pub fn push(&mut self, binding: Tagged<Binding>, default: Option<Tagged<Expr>>) {
        match self.slurp {
            Some(_) => { self.back.push((binding, default)); }
            None => { self.front.push((binding, default)); }
        }
    }
}

#[derive(Debug, Clone)]
pub struct MapBindingElement {
    pub key: Tagged<Key>,
    pub binding: Tagged<Binding>,
    pub default: Option<Tagged<Expr>>,
}

#[derive(Debug, Clone)]
pub struct MapBinding {
    pub elements: Vec<MapBindingElement>,
    pub slurp: Option<usize>,
}

#[derive(Debug, Clone)]
pub enum Transform {
    UnOp(Tagged<UnOp>),
    BinOp(Tagged<BinOp>, Box<Tagged<Expr>>),
    FunCall(Tagged<Vec<Tagged<ArgElement>>>, bool),
}

#[derive(Debug, Clone)]
pub enum StringElement {
    Raw(usize),
    Interpolate(Tagged<Expr>, Option<usize>),
}

#[derive(Debug, Clone)]
pub enum ListElement {
    Singleton(Tagged<Expr>),
    Splat(Tagged<Expr>),
    Cond {
        condition: Tagged<Expr>,
        element: Box<Tagged<ListElement>>,
    },
    Loop {
        binding: Tagged<Binding>,
        iterable: Tagged<Expr>,
        element: Box<Tagged<ListElement>>,
        slots: SlotCatalog,
    },
}

#[derive(Debug, Clone)]
pub enum MapElement {
    Singleton {
        key: Tagged<Expr>,
        value: Tagged<Expr>,
    },
    Splat(Tagged<Expr>),
    Cond {
        condition: Tagged<Expr>,
        element: Box<Tagged<MapElement>>,
    },
    Loop {
        binding: Tagged<Binding>,
        iterable: Tagged<Expr>,
        element: Box<Tagged<MapElement>>,
        slots: SlotCatalog,
    },
}

#[derive(Debug, Clone)]
pub enum ArgElement {
    Singleton(Tagged<Expr>),
    Keyword(Tagged<Key>, Tagged<Expr>),
    Splat(Tagged<Expr>),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Constant(usize),
    String(Vec<StringElement>),
    Slot(BindingLoc),
    Builtin(usize),
    Transformed {
        operand: Box<Tagged<Expr>>,
        transform: Transform,
    },
    List(Vec<Tagged<ListElement>>),
    Map(Vec<Tagged<MapElement>>),
    Let {
        bindings: Vec<(Tagged<Binding>, Tagged<Expr>)>,
        expression: Box<Tagged<Expr>>,
        slots: SlotCatalog,
    },
    Imports {
        imports: Vec<(Tagged<Binding>, Tagged<String>)>,
        expression: Box<Tagged<Expr>>,
        slots: SlotCatalog,
    },
    Branch {
        condition: Box<Tagged<Expr>>,
        true_branch: Box<Tagged<Expr>>,
        false_branch: Box<Tagged<Expr>>,
    },
    Func(Function),
}

#[derive(Debug, Clone)]
pub struct Function {
    pub constants: Vec<Object>,
    pub fmt_specs: Vec<FormatSpec>,
    pub positional: Option<Tagged<ListBinding>>,
    pub keywords: Option<Tagged<MapBinding>>,
    pub expression: Box<Tagged<Expr>>,
    pub slots: SlotCatalog,
    pub requires: Vec<BindingLoc>,
}

impl Function {
    pub fn compile(self) -> Result<CompiledFunction, Error> {
        Compiler::compile(self)
    }
}

pub struct FunctionBuilder<'a> {
    scope: ClosureScope<'a>,
    expression: Option<Tagged<Expr>>,
    positional: Option<Tagged<ListBinding>>,
    keywords: Option<Tagged<MapBinding>>,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(parent: Option<&'a mut dyn Scope>) -> Self {
        Self {
            scope: ClosureScope::new(parent),
            expression: None,
            positional: None,
            keywords: None
        }
    }

    pub fn scope(&mut self) -> &mut ClosureScope<'a> {
        &mut self.scope
    }

    pub fn positional(&mut self, args: Tagged<ListBinding>) {
        self.positional = Some(args);
    }

    pub fn keywords(&mut self, kwargs: Option<Tagged<MapBinding>>) {
        self.keywords = kwargs;
    }

    pub fn expression(&mut self, expr: Tagged<Expr>) {
        self.expression = Some(expr);
    }

    pub fn finalize(self) -> Function {
        let (constants, fmt_specs, requires, slots) = self.scope.finalize();
        Function {
            constants,
            fmt_specs,
            positional: self.positional,
            keywords: self.keywords,
            expression: Box::new(self.expression.unwrap()),
            slots,
            requires,
        }
    }
}

pub struct LetBuilder<'a> {
    scope: LocalScope<'a>,
    bindings: Vec<(Tagged<Binding>, Tagged<Expr>)>,
    expression: Option<Tagged<Expr>>,
}

impl<'a> LetBuilder<'a> {
    pub fn new(parent: &'a mut dyn Scope) -> Self {
        Self {
            scope: LocalScope::new(parent),
            bindings: Vec::new(),
            expression: None,
        }
    }

    pub fn scope(&mut self) -> &mut LocalScope<'a> {
        &mut self.scope
    }

    pub fn add_binding(&mut self, binding: Tagged<Binding>, expr: Tagged<Expr>) {
        self.bindings.push((binding, expr));
    }

    pub fn expression(&mut self, expr: Tagged<Expr>) {
        self.expression = Some(expr);
    }

    pub fn finalize(self) -> Expr {
        let catalog = self.scope.catalog();
        Expr::Let {
            bindings: self.bindings,
            expression: Box::new(self.expression.unwrap()),
            slots: catalog,
        }
    }
}

pub struct ImportsBuilder<'a> {
    scope: LocalScope<'a>,
    imports: Vec<(Tagged<Binding>, Tagged<String>)>,
    expression: Option<Tagged<Expr>>,
}

impl<'a> ImportsBuilder<'a> {
    pub fn new(parent: &'a mut dyn Scope) -> Self {
        Self {
            scope: LocalScope::new(parent),
            imports: Vec::new(),
            expression: None,
        }
    }

    pub fn scope(&mut self) -> &mut LocalScope<'a> {
        &mut self.scope
    }

    pub fn add_import(&mut self, binding: Tagged<Binding>, path: Tagged<String>) {
        self.imports.push((binding, path));
    }

    pub fn expression(&mut self, expr: Tagged<Expr>) {
        self.expression = Some(expr);
    }

    pub fn finalize(self) -> Expr {
        let catalog = self.scope.catalog();
        Expr::Imports {
            imports: self.imports,
            expression: Box::new(self.expression.unwrap()),
            slots: catalog,
        }
    }
}
