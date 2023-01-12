use std::cmp::Ordering;
use std::path::PathBuf;
use std::sync::Arc;

use crate::{eval_file, eval_raw as eval_str};
use crate::ast::*;
use crate::builtins::BUILTINS;
use crate::error::{Error, Internal, Tagged, Unpack, TypeMismatch, Action, Reason};
use crate::object::{Object, Func, Key, Map, List};
use crate::traits::Free;


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
    pub custom: Option<Arc<dyn Fn(&str) -> Result<Option<Object>, Error> + Send + Sync>>,
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


/// The Namespace object is the core type for AST evaluation.
pub enum Namespace<'a> {

    /// Empty namespace - no names bound
    Empty,

    /// Frozen namespace - immutable
    Frozen(&'a Map),

    /// Mutable namespace with a reference to a higher level namespace
    Mutable {
        names: Map,
        prev: &'a Namespace<'a>,
    },
}


impl<'a> Namespace<'a> {

    /// Create a new sub-namespace with no bound names.
    pub fn subtend(&'a self) -> Namespace<'a> {
        Namespace::Mutable { names: Map::new(), prev: self }
    }

    /// Bind a name to an object.
    fn set(&mut self, key: &Key, value: Object) -> Result<(), Error> {
        if let Namespace::Mutable { names, .. } = self {
            names.insert(key.clone(), value);
            Ok(())
        } else {
            // This should never happen.
            Err(Error::new(Internal::SetInFrozenNamespace))
        }
    }

    /// Look up a name in the namespace.
    fn get(&self, key: &Key) -> Result<Object, Error> {
        match self {
            // The top level namespace should always be empty, in which case we
            // pass the ball to the builtins.
            Namespace::Empty => BUILTINS.get(key.as_str()).cloned().map(Object::func).ok_or_else(|| Error::unbound(key.clone())),

            Namespace::Frozen(names) => names.get(key).map(Object::clone).ok_or_else(|| Error::unbound(key.clone())),
            Namespace::Mutable { names, prev } => names.get(key).map(Object::clone).ok_or(()).or_else(|_| prev.get(key))
        }
    }

    /// Match a list of values to a list of list pattern elements. This binds
    /// new names to the namespace.
    pub fn bind_list(&mut self, patterns: &Vec<Tagged<ListPatternElement>>, values: &List) -> Result<(), Error> {
        let mut value_iter = values.iter();

        // In advance, calculate how many values a slurp should capture, in case
        // we encounter one.
        let nslurp = values.len() as i64 - patterns.len() as i64 + 1;

        for pattern_element in patterns {
            match pattern_element.as_ref() {

                // Standard binding
                ListPatternElement::Binding { binding, default } => {

                    // Calculate the next value in the list
                    let val = value_iter.next()
                        .map(Object::clone)
                        .ok_or(())
                        .or_else(|_| {
                            // If none, get the default, or produce the
                            // [`Unpack::ListTooShort`] error.
                            default.as_ref()
                                .ok_or_else(|| Error::new(Unpack::ListTooShort).tag(pattern_element, Action::Bind))
                                .and_then(|node| self.eval(node))
                        })?;

                    // Apply the pattern.
                    self.bind(&binding.pattern, val)?;
                },

                // Anonymous slurp: consume the required number of values, or
                // throw an error if we can't.
                ListPatternElement::Slurp => {
                    for _ in 0..nslurp {
                        if let None = value_iter.next() {
                            return Err(Error::new(Unpack::ListTooShort).tag(pattern_element, Action::Slurp))
                        }
                    }
                },

                // Named slurp: same as above, but assign to a name.
                ListPatternElement::SlurpTo(name) => {
                    let mut values: List = vec![];
                    for _ in 0..nslurp {
                        match value_iter.next() {
                            None => return Err(Error::new(Unpack::ListTooShort).tag(pattern_element, Action::Slurp)),
                            Some(val) => values.push(val.clone()),
                        }
                    }
                    self.set(&*name, Object::list(values))?;
                }
            }
        }

        // At this point, we should have consumed all values. List patterns
        // (unlike map patterns) don't suffer extraneous values.
        if let Some(_) = value_iter.next() {
            Err(Error::new(Unpack::ListTooLong))
        } else {
            Ok(())
        }
    }

    /// Match a map of values to a list of map pattern elements. This binds new
    /// names to the namespace.
    pub fn bind_map(&mut self, patterns: &Vec<Tagged<MapPatternElement>>, values: &Map) -> Result<(), Error> {

        // If we encounter a slurp, change this. The slurp will happen at the end.
        let mut slurp_target: Option<&Key> = None;

        for pattern_element in patterns {
            match pattern_element.as_ref() {

                // Standard binding.
                MapPatternElement::Binding { key, binding, default } => {

                    // Get the value from the map.
                    let val = values.get(key.as_ref())
                        .map(Object::clone)
                        .ok_or(())
                        .or_else(|_| {
                            // If none, get the default, or produce the
                            // [`Unpack::KeyMissing`] error.
                            default.as_ref()
                                .ok_or_else(|| Error::new(Unpack::KeyMissing(key.unwrap())).tag(pattern_element, Action::Bind))
                                .and_then(|node| self.eval(node))
                        })?;

                    // Apply the binding.
                    self.bind(&binding.pattern, val)?;
                },

                // Slurp: remember the target name.
                MapPatternElement::SlurpTo(target) => {
                    slurp_target = Some(target);
                },
            }
        }

        // In case of slurp, we clone the original mapping, then remove all the
        // keys that are explicitly referenced by the other bindings.
        // TODO: Find a more efficient way to do this?
        if let Some(target) = slurp_target {
            let mut values: Map = values.clone();

            for binding_element in patterns {
                if let MapPatternElement::Binding { key, .. } = **binding_element {
                    values.remove(&*key);
                }
            }

            self.set(target, Object::map(values))?;
        }

        Ok(())
    }

    /// Bind a pattern to a value.
    pub fn bind(&mut self, binding: &Tagged<Pattern>, value: Object) -> Result<(), Error> {
        match binding.as_ref() {
            Pattern::Identifier(key) => self.set(&*key, value),
            Pattern::List(bindings) => {
                let list = value.get_list().ok_or_else(
                    || Error::new(Unpack::TypeMismatch(binding.type_of(), value.type_of())).tag(binding, Action::Bind)
                )?;
                self.bind_list(&bindings.0, list).map_err(bindings.tag_error(Action::Bind))
            }
            Pattern::Map(bindings) => {
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
                        sub.bind(&binding.pattern, entry.clone())?;
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
                        sub.bind(&binding.pattern, entry.clone())?;
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

                TopLevel::TypeDef { .. } => {}
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
            Expr::Identifier(name) => self.get(name).map_err(node.tag_error(Action::LookupName)),

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
                for (binding, expr) in bindings {
                    let val = sub.eval(expr)?;
                    sub.bind(&binding.pattern, val)?;
                }
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
            Expr::Function { positional, keywords, expression, .. } => {
                let mut closure: Map = Map::new();
                for ident in node.free() {
                    let val = self.get(&ident)?;
                    closure.insert(ident, val);
                }
                Ok(Object::func(Func {
                    args: positional.clone(),
                    kwargs: keywords.clone(),
                    closure,
                    expr: expression.as_ref().clone(),
                }))
            },
        }
    }
}


/// Evaluate a parsed file AST with given import behavior.
pub fn eval(file: &File, importer: &ImportConfig) -> Result<Object, Error> {
    Namespace::Empty.eval_file(file, importer)
}
