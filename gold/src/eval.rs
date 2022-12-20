use std::cmp::Ordering;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::{eval_file, eval_raw as eval_str};
use crate::ast::*;
use crate::builtins::BUILTINS;
use crate::error::{Error, Internal, Tagged, Unpack, TypeMismatch, FileSystem, Action, Reason};
use crate::object::{Object, Func, Key, Map, List};
use crate::traits::Free;


const STDLIB: &str = include_str!("std.gold");


pub trait ImportResolver {
    fn resolve(&self, path: &str) -> Result<Object, Error>;
}


pub struct StdResolver { }

impl ImportResolver for StdResolver {
    fn resolve(&self, path: &str) -> Result<Object, Error> {
        match path {
            "std" => eval_str(STDLIB),
            _ => Err(Error::new(Reason::UnknownImport(path.to_owned()))),
        }
    }
}


pub struct FileResolver {
    pub root: PathBuf,
}

impl ImportResolver for FileResolver {
    fn resolve(&self, path: &str) -> Result<Object, Error> {
        let target = self.root.join(path);
        eval_file(&target)
    }
}


pub struct ResolveFunc(
    pub Arc<dyn Fn(&str) -> Result<Object, Error> + Send + Sync>
);

pub struct CallableResolver {
    pub resolver: ResolveFunc,
}

impl ImportResolver for CallableResolver {
    fn resolve(&self, path: &str) -> Result<Object, Error> {
        self.resolver.0.as_ref()(path)
    }
}


pub struct SeqResolver<'a> {
    pub resolvers: Vec<Box<&'a dyn ImportResolver>>,
}

impl<'a> ImportResolver for SeqResolver<'a> {
    fn resolve(&self, path: &str) -> Result<Object, Error> {
        for resolver in &self.resolvers {
            if let Ok(obj) = resolver.resolve(path) {
                return Ok(obj)
            }
        }
        Err(Error::new(Reason::UnknownImport(path.to_owned())))
    }
}


pub struct NullResolver {}

impl ImportResolver for NullResolver {
    fn resolve(&self, path: &str) -> Result<Object, Error> {
        Err(Error::new(Reason::UnknownImport(path.to_owned())))
    }
}


pub enum Namespace<'a> {
    Empty,
    Frozen(&'a Map),
    Mutable {
        names: Map,
        prev: &'a Namespace<'a>,
    },
}


impl<'a> Namespace<'a> {
    pub fn subtend(&'a self) -> Namespace<'a> {
        Namespace::Mutable { names: Map::new(), prev: self }
    }

    pub fn set(&mut self, key: &Key, value: Object) -> Result<(), Error> {
        if let Namespace::Mutable { names, .. } = self {
            names.insert(key.clone(), value);
            Ok(())
        } else {
            Err(Error::new(Internal::SetInFrozenNamespace))
        }
    }

    pub fn get(&self, key: &Key) -> Result<Object, Error> {
        match self {
            Namespace::Empty => BUILTINS.get(key.as_str()).cloned().map(Object::function).ok_or_else(|| Error::unbound(key.clone())),
            Namespace::Frozen(names) => names.get(key).map(Object::clone).ok_or_else(|| Error::unbound(key.clone())),
            Namespace::Mutable { names, prev } => names.get(key).map(Object::clone).ok_or(()).or_else(|_| prev.get(key))
        }
    }

    pub fn bind_list(&mut self, bindings: &Vec<Tagged<ListBindingElement>>, values: &List) -> Result<(), Error> {
        let mut value_iter = values.iter();
        let nslurp = values.len() as i64 - bindings.len() as i64 + 1;

        for binding_element in bindings {
            match binding_element.as_ref() {
                ListBindingElement::Binding { binding, default } => {
                    let val = value_iter.next()
                        .map(Object::clone)
                        .ok_or(())
                        .or_else(|_| {
                            default.as_ref()
                                .ok_or_else(|| Error::new(Unpack::ListTooShort).tag(binding_element, Action::Bind))
                                .and_then(|node| self.eval(node))
                        })?;

                    self.bind(&binding, val)?;
                },

                ListBindingElement::Slurp => {
                    for _ in 0..nslurp {
                        if let None = value_iter.next() {
                            return Err(Error::new(Unpack::ListTooShort).tag(binding_element, Action::Slurp))
                        }
                    }
                },

                ListBindingElement::SlurpTo(name) => {
                    let mut values: List = vec![];
                    for _ in 0..nslurp {
                        match value_iter.next() {
                            None => return Err(Error::new(Unpack::ListTooShort).tag(binding_element, Action::Slurp)),
                            Some(val) => values.push(val.clone()),
                        }
                    }
                    self.set(&*name, Object::from(values))?;
                }
            }
        }

        if let Some(_) = value_iter.next() {
            Err(Error::new(Unpack::ListTooLong))
        } else {
            Ok(())
        }
    }

    pub fn bind_map(&mut self, bindings: &Vec<Tagged<MapBindingElement>>, values: &Map) -> Result<(), Error> {
        let mut slurp_target: Option<&Key> = None;

        for binding_element in bindings {
            match binding_element.as_ref() {
                MapBindingElement::Binding { key, binding, default } => {
                    let val = values.get(key.as_ref())
                        .map(Object::clone)
                        .ok_or(())
                        .or_else(|_| {
                            default.as_ref()
                                .ok_or_else(|| Error::new(Unpack::KeyMissing(key.unwrap())).tag(binding_element, Action::Bind))
                                .and_then(|node| self.eval(node))
                        })?;

                    self.bind(&binding, val)?;
                },
                MapBindingElement::SlurpTo(target) => {
                    slurp_target = Some(target);
                },
            }
        }

        if let Some(target) = slurp_target {
            let mut values: Map = values.clone();

            for binding_element in bindings {
                if let MapBindingElement::Binding { key, .. } = **binding_element {
                    values.remove(&*key);
                }
            }

            self.set(target, Object::from(values))?;
        }

        Ok(())
    }

    pub fn bind(&mut self, binding: &Tagged<Binding>, value: Object) -> Result<(), Error> {
        match (binding.as_ref(), &value) {
            (Binding::Identifier(key), val) => {
                self.set(&*key, val.clone())?;
                Ok(())
            },
            (Binding::List(bindings), Object::List(values)) => self.bind_list(&bindings.0, values).map_err(binding.tag_error(Action::Bind)),
            (Binding::Map(bindings), Object::Map(values)) => self.bind_map(&bindings.0, values).map_err(binding.tag_error(Action::Bind)),
            _ => Err(Error::new(Unpack::TypeMismatch(binding.type_of(), value.type_of())).tag(binding, Action::Bind)),
        }
    }

    fn fill_list(&self, element: &ListElement, values: &mut List) -> Result<(), Error> {
        match element {
            ListElement::Singleton(node) => {
                let val = self.eval(node)?;
                values.push(val);
                Ok(())
            }

            ListElement::Splat(node) => {
                let val = self.eval(node)?;
                if let Object::List(from_values) = val {
                    values.extend_from_slice(&*from_values);
                    Ok(())
                } else {
                    Err(Error::new(TypeMismatch::SplatList(val.type_of())).tag(node, Action::Splat))
                }
            },

            ListElement::Cond { condition, element } => {
                if self.eval(condition)?.truthy() {
                    self.fill_list(element, values)
                } else {
                    Ok(())
                }
            },

            ListElement::Loop { binding, iterable, element } => {
                let val = self.eval(iterable)?;
                if let Object::List(from_values) = val {
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

    fn fill_map(&self, element: &Tagged<MapElement>, values: &mut Map) -> Result<(), Error> {
        match element.as_ref() {
            MapElement::Singleton { key, value } => {
                match &self.eval(key)? {
                    Object::Str(k) => {
                        let v = self.eval(value)?;
                        values.insert(Key::from(k), v);
                        Ok(())
                    },
                    k => Err(
                        Error::new(TypeMismatch::MapKey(k.type_of())).tag(key, Action::Assign)
                    ),
                }
            },

            MapElement::Splat(node) => {
                let val = self.eval(node)?;
                if let Object::Map(from_values) = val {
                    for (k, v) in &*from_values {
                        values.insert(k.clone(), v.clone());
                    }
                    Ok(())
                } else {
                    Err(Error::new(TypeMismatch::SplatMap(val.type_of())).tag(node, Action::Splat))
                }
            },

            MapElement::Cond { condition, element } => {
                if self.eval(condition)?.truthy() {
                    self.fill_map(&element, values)
                } else {
                    Ok(())
                }
            },

            MapElement::Loop { binding, iterable, element } => {
                let val = self.eval(iterable)?;
                if let Object::List(from_values) = val {
                    let mut sub = self.subtend();
                    for entry in from_values.as_ref() {
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

    fn fill_args(&self, element: &Tagged<ArgElement>, args: &mut List, kwargs: &mut Map) -> Result<(), Error> {
        match element.as_ref() {
            ArgElement::Singleton(node) => {
                let val = self.eval(node)?;
                args.push(val);
                Ok(())
            },

            ArgElement::Splat(node) => {
                let val = self.eval(node)?;
                match val {
                    Object::List(vals) => {
                        args.extend_from_slice(&vals);
                        Ok(())
                    },
                    Object::Map(vals) => {
                        for (k, v) in vals.as_ref() {
                            kwargs.insert(k.clone(), v.clone());
                        }
                        Ok(())
                    },
                    _ => Err(Error::new(TypeMismatch::SplatArg(val.type_of())).tag(node, Action::Splat)),
                }
            },

            ArgElement::Keyword(key, value) => {
                kwargs.insert(**key, self.eval(value)?);
                Ok(())
            }
        }
    }

    fn operate(&self, operator: &Operator, value: Object) -> Result<Object, Error> {
        match operator {
            Operator::UnOp(op) => {
                match op.as_ref() {
                    UnOp::Passthrough => Ok(value),
                    UnOp::LogicalNegate => Ok(Object::from(!value.truthy())),
                    UnOp::ArithmeticalNegate => value.neg(),
                }.map_err(op.tag_error(Action::Evaluate))
            },

            Operator::BinOp(op, node) => {
                match op.as_ref() {
                    BinOp::And => return if value.truthy() { self.eval(node) } else { Ok(value) },
                    BinOp::Or => return if value.truthy() { Ok(value) } else { self.eval(node) },
                    _ => {},
                }

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
                        .map(|x| Object::from(if **op == BinOp::Less { x } else { !x }))
                    }
                    BinOp::Greater | BinOp::LessEqual => {
                        value.cmp_bool(&rhs, Ordering::Greater)
                        .ok_or_else(|| Error::new(TypeMismatch::BinOp(value.type_of(), rhs.type_of(), **op)))
                        .map(|x| Object::from(if **op == BinOp::Greater { x } else { !x }))
                    }
                    BinOp::Equal => Ok(Object::from(value.user_eq(&rhs))),
                    BinOp::NotEqual => Ok(Object::from(!value.user_eq(&rhs))),
                    BinOp::Index => value.index(&self.eval(node)?),

                    // Unreachable
                    BinOp::And | BinOp::Or => { Err(Error::new(Reason::None)) },
                }.map_err(op.tag_error(Action::Evaluate))
            },

            Operator::FunCall(elements) => {
                let mut call_args: List = vec![];
                let mut call_kwargs: Map = Map::new();
                for element in elements.as_ref() {
                    self.fill_args(element, &mut call_args, &mut call_kwargs)?;
                }
                value.call(&call_args, Some(&call_kwargs)).map_err(elements.tag_error(Action::Evaluate))
            },
        }
    }

    pub fn eval_file<T: ImportResolver>(&mut self, file: &File, importer: &T) -> Result<Object, Error> {
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

    pub fn eval(&self, node: &Tagged<Expr>) -> Result<Object, Error> {
        match node.as_ref() {
            Expr::Literal(val) => Ok(val.clone()),

            Expr::String(elements) => {
                let mut rval = String::new();
                for element in elements {
                    match element {
                        StringElement::Raw(val) => rval += val.as_ref(),
                        StringElement::Interpolate(expr) => {
                            let val = self.eval(expr)?;
                            let text = val.format().map_err(expr.tag_error(Action::Format))?;
                            rval += &text;
                        }
                    }
                }
                Ok(Object::natural_string(rval))
            },

            Expr::Identifier(name) => self.get(name).map_err(node.tag_error(Action::LookupName)),

            Expr::List(elements) => {
                let mut values: List = vec![];
                for element in elements {
                    self.fill_list(element, &mut values)?;
                }
                Ok(Object::from(values))
            },

            Expr::Map(elements) => {
                let mut values: Map = Map::new();
                for element in elements {
                    self.fill_map(element, &mut values)?;
                }
                Ok(Object::from(values))
            }

            Expr::Let { bindings, expression } => {
                let mut sub = self.subtend();
                for (binding, expr) in bindings {
                    let val = sub.eval(expr)?;
                    sub.bind(binding, val)?;
                }
                sub.eval(expression)
            },

            Expr::Operator { operand, operator } => {
                let x = self.eval(operand)?;
                self.operate(operator, x)
            },

            Expr::Branch { condition, true_branch, false_branch } => {
                let cond = self.eval(condition)?;
                if cond.truthy() {
                    self.eval(true_branch)
                } else {
                    self.eval(false_branch)
                }
            },

            Expr::Function { positional, keywords, expression } => {
                let mut closure: Map = Map::new();
                for ident in node.free() {
                    let val = self.get(&ident)?;
                    closure.insert(ident, val);
                }
                Ok(Object::function(Func {
                    args: positional.clone(),
                    kwargs: keywords.clone(),
                    closure,
                    expr: expression.as_ref().clone(),
                }))
            },
        }
    }
}


pub fn eval_raw<T: ImportResolver>(file: &File, resolver: &T) -> Result<Object, Error> {
    let resolver = SeqResolver {
        resolvers: vec![
            Box::new(&StdResolver {}),
            Box::new(resolver),
        ],
    };
    Namespace::Empty.eval_file(file, &resolver)
}


pub fn eval_path<T: ImportResolver>(file: &File, path: &Path, resolver: &T) -> Result<Object, Error> {
    let parent = path.parent().ok_or_else(|| Error::new(FileSystem::NoParent(path.to_owned())))?;
    let file_resolver = FileResolver { root: parent.to_owned() };
    let resolver = SeqResolver {
        resolvers: vec![
            Box::new(&StdResolver {}),
            Box::new(resolver),
            Box::new(&file_resolver),
        ],
    };
    Namespace::Empty.eval_file(file, &resolver)
}
