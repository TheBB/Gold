use std::cmp::Ordering;
use std::collections::HashSet;
use std::path::PathBuf;
use std::rc::Rc;

use crate::compile::{Function, Instruction};
use crate::{eval_file, eval_raw as eval_str};
use crate::ast::*;
use crate::builtins::BUILTINS;
use crate::error::{Error, Internal, Tagged, Unpack, TypeMismatch, Action, Reason};
use crate::object::{Object, Key, Map, List};
use crate::traits::{Bound, Free};


/// Source code of the standard library (imported under the name 'std')
const STDLIB: &str = include_str!("std.gold");


/// Configure the import behavior when evaluating Gold code.
#[derive(Clone, Default)]
pub struct ImportConfig {
    /// If set, unresolved imports will be loaded relative to this path.
    pub root_path: Option<PathBuf>,

    /// If set, this function will be called to resolve unknown imports.
    ///
    /// It should return Ok(None) to indicate that the path was unknown. In this
    /// case, the importer will attempt to resolve the import to a path if
    /// possible. If the function returns an error, import resolution will be
    /// aborted.
    pub custom: Option<Rc<dyn Fn(&str) -> Result<Option<Object>, Error>>>,
}

impl ImportConfig {
    /// Construct a new import config with a relative path but no custom
    /// import behavior.
    pub fn with_path(path: PathBuf) -> Self {
        Self {
            root_path: Some(path),
            ..Default::default()
        }
    }

    /// Resolve an import path.
    fn resolve(&self, path: &str) -> Result<Object, Error> {
        // Gold reserves all import paths starting with 'std'
        if path.starts_with("std") {
            match path {
                "std" => eval_str(STDLIB),
                _ => Err(Error::new(Reason::UnknownImport(path.to_owned())))
            }
        } else {
            // The custom import resolver has precedence over paths
            if let Some(resolver) = &self.custom {
                if let Some(result) = resolver(path)? {
                    return Ok(result)
                }
            }

            // Import by path
            if let Some(root) = &self.root_path {
                let target = root.join(path);
                eval_file(&target)
            } else {
                Err(Error::new(Reason::UnknownImport(path.to_owned())))
            }
        }
    }
}


/// Status of a name binding.
pub(crate) enum BindingResult {
    /// Name is not bound
    Unbound(Error),

    /// Name is bound
    Bound(Object),

    /// Name is not bound yet, but expected to be bound soon
    Expected(Error),
}

impl BindingResult {
    pub(crate) fn to_result_immediate(self) -> Result<Object, Error> {
        match self {
            Self::Bound(obj) => Ok(obj),
            Self::Unbound(err) => Err(err),
            Self::Expected(err) => Err(err),
        }
    }

    pub(crate) fn to_result_deferred(self) -> Result<Option<Object>, Error> {
        match self {
            Self::Bound(obj) => Ok(Some(obj)),
            Self::Unbound(err) => Err(err),
            Self::Expected(_) => Ok(None),
        }
    }
}

impl From<Result<Object, Error>> for BindingResult {
    fn from(value: Result<Object, Error>) -> Self {
        match value {
            Ok(obj) => BindingResult::Bound(obj),
            Err(err) => BindingResult::Unbound(err),
        }
    }
}


/// The Namespace object is the core type for AST evaluation.
pub(crate) enum Namespace<'a> {
    /// Empty namespace - no names bound
    Empty,

    /// Frozen namespace - immutable
    Frozen(&'a Map),

    /// Mutable namespace with a reference to a higher level namespace
    Mutable {
        names: Map,
        expected: HashSet<Key>,
        prev: &'a Namespace<'a>,
    },
}


impl<'a> Namespace<'a> {
    /// Create a new sub-namespace with no bound names.
    pub fn subtend(&'a self) -> Namespace<'a> {
        Namespace::Mutable { names: Map::new(), expected: HashSet::new(), prev: self }
    }

    /// Bind a name to an object.
    fn set(&mut self, key: &Key, value: Object) -> Result<(), Error> {
        if let Namespace::Mutable { names, .. } = self {
            names.insert(*key, value);
            Ok(())
        } else {
            // This should never happen.
            Err(Error::new(Internal::SetInFrozenNamespace))
        }
    }

    /// Signify that a name is expected to be bound.
    fn expect(&mut self, key: &Key) -> Result<(), Error> {
        if let Namespace::Mutable { expected, .. } = self {
            expected.insert(*key);
            Ok(())
        } else {
            Err(Error::new(Internal::SetInFrozenNamespace))
        }
    }

    pub(crate) fn get_immediate(&self, key: &Key) -> Result<Object, Error> {
        self.get_impl(key, false).to_result_immediate()
    }

    fn get_deferred(&self, key: &Key) -> Result<Option<Object>, Error> {
        self.get_impl(key, true).to_result_deferred()
    }

    /// Look up a name in the namespace.
    fn get_impl(&self, key: &Key, allow_deferred: bool) -> BindingResult {
        match self {
            // The top level namespace should always be empty, in which case we
            // pass the ball to the builtins.
            Namespace::Empty => BUILTINS.get(key.as_str()).cloned().map(Object::func).ok_or_else(|| Error::unbound(key.clone())).into(),
            Namespace::Frozen(names) => names.get(key).map(Object::clone).ok_or_else(|| Error::unbound(key.clone())).into(),
            Namespace::Mutable { names, expected, prev } => {
                if let Some(obj) = names.get(key) {
                    BindingResult::Bound(obj.clone())
                } else if expected.contains(key) && allow_deferred {
                    BindingResult::Expected(Error::unbound(*key))
                } else {
                    prev.get_impl(key, allow_deferred)
                }
            }
        }
    }

    /// Resolve all deferred bindings in closures.
    fn resolve_deferred(&self) -> Result<(), Error> {
        if let Namespace::Mutable { names, .. } = self {
            for (_, obj) in names.iter() {
                obj.resolve_deferred(self)?;
            }
        }

        Ok(())
    }

    /// Match a list of values to a list of list binding elements. This binds
    /// new names to the namespace.
    pub fn bind_list(&mut self, bindings: &Vec<Tagged<ListBindingElement>>, values: &List) -> Result<(), Error> {
        let mut value_iter = values.iter();

        // In advance, calculate how many values a slurp should capture, in case
        // we encounter one.
        let nslurp = values.len() as i64 - bindings.len() as i64 + 1;

        for binding_element in bindings {
            match binding_element.as_ref() {

                // Standard binding
                ListBindingElement::Binding { binding, default } => {

                    // Calculate the next value in the list
                    let val = value_iter.next()
                        .map(Object::clone)
                        .ok_or(())
                        .or_else(|_| {
                            // If none, get the default, or produce the
                            // [`Unpack::ListTooShort`] error.
                            default.as_ref()
                                .ok_or_else(|| Error::new(Unpack::ListTooShort).tag(binding_element, Action::Bind))
                                .and_then(|node| self.eval(node))
                        })?;

                    // Apply the binding.
                    self.bind(&binding, val)?;
                },

                // Anonymous slurp: consume the required number of values, or
                // throw an error if we can't.
                ListBindingElement::Slurp => {
                    for _ in 0..nslurp {
                        if let None = value_iter.next() {
                            return Err(Error::new(Unpack::ListTooShort).tag(binding_element, Action::Slurp))
                        }
                    }
                },

                // Named slurp: same as above, but assign to a name.
                ListBindingElement::SlurpTo(name) => {
                    let mut values: List = vec![];
                    for _ in 0..nslurp {
                        match value_iter.next() {
                            None => return Err(Error::new(Unpack::ListTooShort).tag(binding_element, Action::Slurp)),
                            Some(val) => values.push(val.clone()),
                        }
                    }
                    self.set(&*name, Object::list(values))?;
                }
            }
        }

        // At this point, we should have consumed all values. List bindings
        // (unlike map bindings) don't suffer extraneous values.
        if let Some(_) = value_iter.next() {
            Err(Error::new(Unpack::ListTooLong))
        } else {
            Ok(())
        }
    }

    /// Match a map of values to a list of map binding elements. This binds new
    /// names to the namespace.
    pub fn bind_map(&mut self, bindings: &Vec<Tagged<MapBindingElement>>, values: &Map) -> Result<(), Error> {
        // If we encounter a slurp, change this. The slurp will happen at the end.
        let mut slurp_target: Option<&Key> = None;

        for binding_element in bindings {
            match binding_element.as_ref() {

                // Standard binding.
                MapBindingElement::Binding { key, binding, default } => {

                    // Get the value from the map.
                    let val = values.get(key.as_ref())
                        .map(Object::clone)
                        .ok_or(())
                        .or_else(|_| {
                            // If none, get the default, or produce the
                            // [`Unpack::KeyMissing`] error.
                            default.as_ref()
                                .ok_or_else(|| Error::new(Unpack::KeyMissing(key.unwrap())).tag(binding_element, Action::Bind))
                                .and_then(|node| self.eval(node))
                        })?;

                    // Apply the binding.
                    self.bind(&binding, val)?;
                },

                // Slurp: remember the target name.
                MapBindingElement::SlurpTo(target) => {
                    slurp_target = Some(target);
                },
            }
        }

        // In case of slurp, we clone the original mapping, then remove all the
        // keys that are explicitly referenced by the other bindings.
        // TODO: Find a more efficient way to do this?
        if let Some(target) = slurp_target {
            let mut values: Map = values.clone();

            for binding_element in bindings {
                if let MapBindingElement::Binding { key, .. } = **binding_element {
                    values.remove(&*key);
                }
            }

            self.set(target, Object::map(values))?;
        }

        Ok(())
    }

    /// Bind a pattern to a value.
    pub fn bind(&mut self, binding: &Tagged<Binding>, value: Object) -> Result<(), Error> {
        match binding.as_ref() {
            Binding::Identifier(key) => self.set(&*key, value),
            Binding::List(bindings) => {
                let list = value.get_list().ok_or_else(
                    || Error::new(Unpack::TypeMismatch(binding.type_of(), value.type_of())).tag(binding, Action::Bind)
                )?;
                self.bind_list(&bindings.0, list).map_err(bindings.tag_error(Action::Bind))
            }
            Binding::Map(bindings) => {
                let obj = value.get_map().ok_or_else(
                    || Error::new(Unpack::TypeMismatch(binding.type_of(), value.type_of())).tag(binding, Action::Bind)
                )?;
                self.bind_map(&bindings.0, obj).map_err(bindings.tag_error(Action::Bind))
            }
        }
    }

    /// Evaluate a list element and accumulate values in a list.
    fn fill_list(&self, element: &ListElement, values: &mut List) -> Result<(), Error> {
        match element {
            // Singleton element: just evaluate it and add.
            ListElement::Singleton(node) => {
                let val = self.eval(node)?;
                values.push(val);
                Ok(())
            }

            // Splat: evaluate the expression, then add all its elements to the list.
            ListElement::Splat(node) => {
                let val = self.eval(node)?;
                if let Some(from_values) = val.get_list() {
                    values.extend_from_slice(&*from_values);
                    Ok(())
                } else {
                    Err(Error::new(TypeMismatch::SplatList(val.type_of())).tag(node, Action::Splat))
                }
            },

            // Conditional element: evaluate the condition then recurse.
            ListElement::Cond { condition, element } => {
                if self.eval(condition)?.truthy() {
                    self.fill_list(element, values)
                } else {
                    Ok(())
                }
            },

            // Iterated element: evaluate the iterable, loop over its elements,
            // bind to a pattern and then recurse.
            ListElement::Loop { binding, iterable, element } => {
                let val = self.eval(iterable)?;
                if let Some(from_values) = val.get_list() {
                    let mut sub = self.subtend();
                    for entry in &*from_values {
                        sub.bind(binding, entry.clone())?;
                        sub.fill_list(element, values)?;
                    }
                    Ok(())
                } else {
                    Err(Error::new(TypeMismatch::Iterate(val.type_of())).tag(iterable, Action::Iterate))
                }
            }
        }
    }

    /// Evaluate a map element and accumulate values in a map.
    fn fill_map(&self, element: &Tagged<MapElement>, values: &mut Map) -> Result<(), Error> {
        match element.as_ref() {
            // Siengleton element: just evaluate it and insert.
            MapElement::Singleton { key, value } => {
                let k = self.eval(key)?;
                if let Some(k) = k.get_key() {
                    let v = self.eval(value)?;
                    values.insert(k, v);
                    Ok(())
                } else {
                    Err(Error::new(TypeMismatch::MapKey(k.type_of())).tag(key, Action::Assign))
                }
            },

            // Splat: evaluate the expression, then insert all its pairs in the map.
            MapElement::Splat(node) => {
                let val = self.eval(node)?;
                if let Some(from_values) = val.get_map() {
                    for (k, v) in &*from_values {
                        values.insert(k.clone(), v.clone());
                    }
                    Ok(())
                } else {
                    Err(Error::new(TypeMismatch::SplatMap(val.type_of())).tag(node, Action::Splat))
                }
            },

            // Conditional element: evaluate the condition then recurse.
            MapElement::Cond { condition, element } => {
                if self.eval(condition)?.truthy() {
                    self.fill_map(&element, values)
                } else {
                    Ok(())
                }
            },

            // Iterated element: evaluate the iterable, loop over its elements,
            // biend to a pattern and then recurse.
            MapElement::Loop { binding, iterable, element } => {
                let val = self.eval(iterable)?;
                if let Some(from_values) = val.get_list() {
                    let mut sub = self.subtend();
                    for entry in from_values {
                        sub.bind(&binding, entry.clone())?;
                        sub.fill_map(element, values)?;
                    }
                    Ok(())
                } else {
                    Err(Error::new(TypeMismatch::Iterate(val.type_of())).tag(iterable, Action::Iterate))
                }
            }
        }
    }

    /// Evaluate a function argument element and accumulate values in a list or a map.
    fn fill_args(&self, element: &Tagged<ArgElement>, args: &mut List, kwargs: &mut Map) -> Result<(), Error> {
        match element.as_ref() {
            // Singletons are positional arguments.
            ArgElement::Singleton(node) => {
                let val = self.eval(node)?;
                args.push(val);
            },

            // Keyword elements are keyword arguments.
            ArgElement::Keyword(key, value) => {
                kwargs.insert(**key, self.eval(value)?);
            }

            // Splats can be either positional or keyword, depending on the type
            // of the value.
            ArgElement::Splat(node) => {
                let val = self.eval(node)?;
                if let Some(list) = val.get_list() {
                    args.extend_from_slice(list);
                } else if let Some(obj) = val.get_map() {
                    for (k, v) in obj {
                        kwargs.insert(k.clone(), v.clone());
                    }
                } else {
                    return Err(Error::new(TypeMismatch::SplatArg(val.type_of())).tag(node, Action::Splat))
                }
            },
        }

        Ok(())
    }

    /// Evaluate a transform (an operator, typically) applied to a value.
    fn transform(&self, transform: &Transform, value: Object) -> Result<Object, Error> {
        match transform {
            // Unary operators
            Transform::UnOp(op) => {
                match op.as_ref() {
                    UnOp::Passthrough => Ok(value),
                    UnOp::LogicalNegate => Ok(Object::bool(!value.truthy())),
                    UnOp::ArithmeticalNegate => value.neg(),
                }.map_err(op.tag_error(Action::Evaluate))
            },

            // Binary operators
            Transform::BinOp(op, node) => {

                // Short-circuiting operators
                match op.as_ref() {
                    BinOp::And => return if value.truthy() { self.eval(node) } else { Ok(value) },
                    BinOp::Or => return if value.truthy() { Ok(value) } else { self.eval(node) },
                    _ => {},
                }

                // All others
                let rhs = self.eval(node)?;
                match op.as_ref() {
                    BinOp::Add => value.add(&rhs),
                    BinOp::Subtract => value.sub(&rhs),
                    BinOp::Multiply => value.mul(&rhs),
                    BinOp::Divide => value.div(&rhs),
                    BinOp::IntegerDivide => value.idiv(&rhs),
                    BinOp::Power => value.pow(&rhs),
                    BinOp::Less | BinOp::GreaterEqual => {
                        value.cmp_bool(&rhs, Ordering::Less)
                        .ok_or_else(|| Error::new(TypeMismatch::BinOp(value.type_of(), rhs.type_of(), **op)))
                        .map(|x| Object::bool(if **op == BinOp::Less { x } else { !x }))
                    }
                    BinOp::Greater | BinOp::LessEqual => {
                        value.cmp_bool(&rhs, Ordering::Greater)
                        .ok_or_else(|| Error::new(TypeMismatch::BinOp(value.type_of(), rhs.type_of(), **op)))
                        .map(|x| Object::bool(if **op == BinOp::Greater { x } else { !x }))
                    }
                    BinOp::Equal => Ok(Object::bool(value.user_eq(&rhs))),
                    BinOp::NotEqual => Ok(Object::bool(!value.user_eq(&rhs))),
                    BinOp::Contains => Ok(Object::bool(value.contains(&rhs)?)),
                    BinOp::Index => value.index(&self.eval(node)?),

                    // Unreachable
                    BinOp::And | BinOp::Or => { Err(Error::new(Reason::None)) },
                }.map_err(op.tag_error(Action::Evaluate))
            },

            // Function call
            Transform::FunCall(elements) => {
                let mut call_args: List = vec![];
                let mut call_kwargs: Map = Map::new();
                for element in elements.as_ref() {
                    self.fill_args(element, &mut call_args, &mut call_kwargs)?;
                }
                value.call(&call_args, Some(&call_kwargs)).map_err(elements.tag_error(Action::Evaluate))
            },
        }
    }

    // Evaluate a file: a sequence of top-level statements followed by an
    // expression.
    fn eval_file(&mut self, file: &File, importer: &ImportConfig) -> Result<Object, Error> {
        let mut ns = self.subtend();
        for statement in &file.statements {
            match statement {
                TopLevel::Import(path, binding) => {
                    let object = importer.resolve(path.as_ref()).map_err(path.tag_error(Action::Import))?;
                    ns.bind(binding, object)?;
                }
            }
        }
        ns.eval(&file.expression)
    }

    // Evaluate an expression.
    pub fn eval(&self, node: &Tagged<Expr>) -> Result<Object, Error> {
        match node.as_ref() {
            // Literal values: just clone and return.
            Expr::Literal(val) => Ok(val.clone()),

            // A string is a sequence of string elements, either raw data or
            // interpolated expressions.
            Expr::String(elements) => {
                let mut rval = String::new();
                for element in elements {
                    match element {
                        StringElement::Raw(val) => rval += val.as_ref(),
                        StringElement::Interpolate(expr, spec) => {
                            let val = self.eval(expr)?;
                            let text = val.format(spec.clone().unwrap_or_default()).map_err(expr.tag_error(Action::Format))?;
                            rval += &text;
                        }
                    }
                }
                Ok(Object::str_natural(rval))
            },

            // Look up an identifier by name.
            Expr::Identifier(name) => self.get_immediate(name).map_err(node.tag_error(Action::LookupName)),

            // A list should be evaluated by accumulating all its list elements.
            Expr::List(elements) => {
                let mut values: List = vec![];
                for element in elements {
                    self.fill_list(element, &mut values)?;
                }
                Ok(Object::list(values))
            },

            // A map should be evaluated by accumulating all its map elements.
            Expr::Map(elements) => {
                let mut values: Map = Map::new();
                for element in elements {
                    self.fill_map(element, &mut values)?;
                }
                Ok(Object::map(values))
            }

            // Bindings in a let-block must be bound in a sub-namespace to avoid
            // cluttering this one.
            Expr::Let { bindings, expression } => {
                let mut sub = self.subtend();
                for (binding, _) in bindings {
                    for key in binding.bound() {
                        sub.expect(&key)?;
                    }
                }
                for (binding, expr) in bindings {
                    let val = sub.eval(expr)?;
                    sub.bind(binding, val)?;
                }

                sub.resolve_deferred()?;
                sub.eval(expression)
            },

            // Transforms and operator expressions are forwarded to the `transform` method.
            Expr::Transformed { operand, transform } => {
                let x = self.eval(operand)?;
                self.transform(transform, x)
            },

            // Conditional branches.
            Expr::Branch { condition, true_branch, false_branch } => {
                let cond = self.eval(condition)?;
                if cond.truthy() {
                    self.eval(true_branch)
                } else {
                    self.eval(false_branch)
                }
            },

            // Function definitions: capture all free variables in the function
            // in a closure.
            Expr::Function { positional, keywords, expression } => {
                let mut closure: Map = Map::new();
                let mut deferred: Option<HashSet<Key>> = None;

                for ident in node.free() {
                    match self.get_deferred(&ident)? {
                        Some(obj) => { closure.insert(ident, obj); },
                        None => deferred = deferred.map_or_else(
                            || { let mut d = HashSet::new(); d.insert(ident); Some(d) },
                            |mut d| { d.insert(ident); Some(d) }
                        ),
                    }
                }

                Ok(Object::int(1))

                // Ok(Object::func(Func {
                //     args: positional.clone(),
                //     kwargs: keywords.clone(),
                //     closure,
                //     deferred,
                //     expr: expression.as_ref().clone(),
                // }))
            },
        }
    }
}


/// Evaluate a parsed file AST with given import behavior.
pub fn eval(file: &File, importer: &ImportConfig) -> Result<Object, Error> {
    Namespace::Empty.eval_file(file, importer)
}


pub(crate) struct Frame<'a> {
    pub function: &'a Function,
    pub stack: Vec<Object>,
    pub ip: usize,
}

impl<'a> Frame<'a> {
    pub fn new(function: &'a Function) -> Frame {
        Frame { function, stack: vec![], ip: 0 }
    }

    pub fn next_instruction(&mut self) -> Instruction {
        self.ip += 1;
        self.function.code[self.ip - 1]
    }
}


pub(crate) struct Vm<'a> {
    frames: Vec<Frame<'a>>,
    fp: usize,
}

impl<'a> Vm<'a> {
    pub fn new() -> Self {
        Self { frames: vec![], fp: 0 }
    }

    pub fn eval(&mut self, function: &'a Function) -> Result<Object, Error> {
        self.frames.push(Frame::new(function));
        self.fp = 0;
        self.eval_impl()
    }

    fn eval_impl(&mut self) -> Result<Object, Error> {
        loop {
            let instruction = self.cur_frame().next_instruction();
            match instruction {
                Instruction::LoadConst(i) => {
                    let obj = self.cur_frame().function.constants[i].clone();
                    self.push(obj);
                }

                Instruction::Return => {
                    let obj = self.pop();
                    self.frames.pop();
                    if self.fp == 0 {
                        return Ok(obj)
                    } else {
                        self.fp -= 1;
                        self.push(obj);
                    }
                }

                Instruction::CondJump(delta) => {
                    let obj = self.pop();
                    if obj.truthy() {
                        self.cur_frame().ip += delta;
                    }
                }

                Instruction::Jump(delta) => {
                    self.cur_frame().ip += delta;
                }

                Instruction::Duplicate => {
                    let obj = self.peek().clone();
                    self.push(obj);
                }

                Instruction::Discard => {
                    self.pop();
                }

                Instruction::Noop => {}

                Instruction::ArithmeticalNegate => {
                    let obj = self.pop();
                    self.push(obj.neg()?);
                }

                Instruction::LogicalNegate => {
                    let obj = self.pop();
                    self.push(Object::bool(!obj.truthy()));
                }

                Instruction::Add => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.add(&rhs)?);
                }

                Instruction::Subtract => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.sub(&rhs)?);
                }

                Instruction::Multiply => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.mul(&rhs)?);
                }

                Instruction::IntegerDivide => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.idiv(&rhs)?);
                }

                Instruction::Divide => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.div(&rhs)?);
                }

                Instruction::Power => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.pow(&rhs)?);
                }

                Instruction::Less => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Less)
                        .ok_or_else(|| Error::new(TypeMismatch::BinOp(lhs.type_of(), rhs.type_of(), BinOp::Less)))
                        .map(Object::bool)?;
                    self.push(res);
                }

                Instruction::Greater => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Greater)
                        .ok_or_else(|| Error::new(TypeMismatch::BinOp(lhs.type_of(), rhs.type_of(), BinOp::Greater)))
                        .map(Object::bool)?;
                    self.push(res);
                }

                Instruction::LessEqual => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Greater)
                        .ok_or_else(|| Error::new(TypeMismatch::BinOp(lhs.type_of(), rhs.type_of(), BinOp::LessEqual)))
                        .map(|x| Object::bool(!x))?;
                    self.push(res);
                }

                Instruction::GreaterEqual => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Less)
                        .ok_or_else(|| Error::new(TypeMismatch::BinOp(lhs.type_of(), rhs.type_of(), BinOp::GreaterEqual)))
                        .map(|x| Object::bool(!x))?;
                    self.push(res);
                }

                Instruction::Equal => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(Object::bool(lhs.user_eq(&rhs)));
                }

                Instruction::NotEqual => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(Object::bool(!lhs.user_eq(&rhs)));
                }

                Instruction::Contains => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(Object::bool(lhs.contains(&rhs)?));
                }

                Instruction::NewList => {
                    self.push(Object::new_list());
                }

                Instruction::NewMap => {
                    self.push(Object::new_map());
                }
            }
        }
    }

    fn cur_frame(&mut self) -> &mut Frame<'a> {
        &mut self.frames[self.fp]
    }

    fn peek(&mut self) -> &Object {
        self.cur_frame().stack.last().unwrap()
    }

    fn pop(&mut self) -> Object {
        self.cur_frame().stack.pop().unwrap()
    }

    fn push(&mut self, obj: Object) {
        self.cur_frame().stack.push(obj)
    }
}
