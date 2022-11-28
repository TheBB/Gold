use std::cmp::Ordering;
use std::path::{Path, PathBuf};
use std::ops::Not;
use std::sync::Arc;

use crate::{eval_file, eval_raw as eval_str};
use crate::ast::*;
use crate::builtins::BUILTINS;
use crate::error::{Error, InternalErrorReason, Tagged};
use crate::object::{Object, Function, Key, Map, List};
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
            _ => Err(Error::default()),
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
        Err(Error::default())
    }
}


pub struct NullResolver {}

impl ImportResolver for NullResolver {
    fn resolve(&self, _: &str) -> Result<Object, Error> {
        Err(Error::default())
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
            Err(Error::with_reason(InternalErrorReason::SetInFrozenNamespace))
        }
    }

    pub fn get(&self, key: &Key) -> Result<Object, Error> {
        match self {
            Namespace::Empty => BUILTINS.get(key.as_str()).cloned().map(Object::from).ok_or_else(|| Error::unbound(key.clone())),
            Namespace::Frozen(names) => names.get(key).map(Object::clone).ok_or_else(|| Error::unbound(key.clone())),
            Namespace::Mutable { names, prev } => names.get(key).map(Object::clone).ok_or(()).or_else(|_| prev.get(key))
        }
    }

    pub fn bind_list<T: AsRef<ListBindingElement>>(&mut self, bindings: &Vec<T>, values: &List) -> Result<(), Error> {
        let mut value_iter = values.iter();
        let nslurp = values.len() as i64 - bindings.len() as i64 + 1;

        for binding_element in bindings {
            match binding_element.as_ref() {
                ListBindingElement::Binding { binding, default } => {
                    let val = value_iter.next()
                        .map(Object::clone)
                        .ok_or_else(|| "not enough elements".to_string())
                        .or_else(|_| {
                            default.as_ref()
                                .ok_or_else(|| Error::default())
                                .and_then(|node| self.eval(node))
                        })?;

                    self.bind(binding.as_ref(), val)?;
                },

                ListBindingElement::Slurp => {
                    for _ in 0..nslurp {
                        if let None = value_iter.next() {
                            return Err(Error::default())
                        }
                    }
                },

                ListBindingElement::SlurpTo(name) => {
                    let mut values: List = vec![];
                    for _ in 0..nslurp {
                        match value_iter.next() {
                            None => return Err(Error::default()),
                            Some(val) => values.push(val.clone()),
                        }
                    }
                    self.set(name.as_ref(), Object::from(values))?;
                }
            }
        }

        if let Some(_) = value_iter.next() {
            Err(Error::default())
        } else {
            Ok(())
        }
    }

    pub fn bind_map<T: AsRef<MapBindingElement>>(&mut self, bindings: &Vec<T>, values: &Map) -> Result<(), Error> {
        let mut slurp_target: Option<&Key> = None;

        for binding_element in bindings {
            match binding_element.as_ref() {
                MapBindingElement::Binding { key, binding, default } => {
                    let val = values.get(key.as_ref())
                        .map(Object::clone)
                        .ok_or_else(|| "zomg".to_string())
                        .or_else(|_| {
                            default.as_ref()
                                .ok_or_else(|| Error::default())
                                .and_then(|node| self.eval(node))
                        })?;

                    self.bind(binding.as_ref(), val)?;
                },
                MapBindingElement::SlurpTo(target) => {
                    slurp_target = Some(target.as_ref());
                },
            }
        }

        if let Some(target) = slurp_target {
            let mut values: Map = values.clone();

            for binding_element in bindings {
                if let MapBindingElement::Binding { key, .. } = binding_element.as_ref() {
                    values.remove(key.as_ref());
                }
            }

            self.set(target, Object::from(values))?;
        }

        Ok(())
    }

    pub fn bind(&mut self, binding: &Binding, value: Object) -> Result<(), Error> {
        match (binding, value) {
            (Binding::Identifier(key), val) => {
                self.set(key.as_ref(), val)?;
                Ok(())
            },
            (Binding::List(bindings), Object::List(values)) => self.bind_list(&bindings.as_ref().0, values.as_ref()),
            (Binding::Map(bindings), Object::Map(values)) => self.bind_map(&bindings.as_ref().0, values.as_ref()),
            _ => Err(Error::default()),
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
                    Err(Error::default())
                }
            },

            ListElement::Cond { condition, element } => {
                if self.eval(condition)?.truthy() {
                    self.fill_list(element.as_ref().as_ref(), values)
                } else {
                    Ok(())
                }
            },

            ListElement::Loop { binding, iterable, element } => {
                if let Object::List(from_values) = self.eval(iterable)? {
                    let mut sub = self.subtend();
                    for entry in &*from_values {
                        sub.bind(binding.as_ref(), entry.clone())?;
                        sub.fill_list(element.as_ref().as_ref(), values)?;
                    }
                    Ok(())
                } else {
                    Err(Error::default())
                }
            }
        }
    }

    fn fill_map(&self, element: &Tagged<MapElement>, values: &mut Map) -> Result<(), Error> {
        match element.as_ref() {
            MapElement::Singleton { key, value } => {
                if let Object::IntString(k) = self.eval(key)? {
                    let v = self.eval(value)?;
                    values.insert(k, v);
                    Ok(())
                } else {
                    Err(Error::default())
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
                    Err(Error::default())
                }
            },

            MapElement::Cond { condition, element } => {
                if self.eval(condition)?.truthy() {
                    self.fill_map(element, values)
                } else {
                    Ok(())
                }
            },

            MapElement::Loop { binding, iterable, element } => {
                if let Object::List(from_values) = self.eval(iterable)? {
                    let mut sub = self.subtend();
                    for entry in &*from_values {
                        sub.bind(binding.as_ref(), entry.clone())?;
                        sub.fill_map(element.as_ref(), values)?;
                    }
                    Ok(())
                } else {
                    Err(Error::default())
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
                    _ => Err(Error::default()),
                }
            },

            ArgElement::Keyword(key, value) => {
                kwargs.insert(*key.as_ref(), self.eval(value)?);
                Ok(())
            }
        }
    }

    fn operate(&self, operator: &Operator, value: Object) -> Result<Object, Error> {
        match operator {
            Operator::UnOp(UnOp::Passthrough) => Ok(value),
            Operator::UnOp(UnOp::LogicalNegate) => Ok(Object::from(!value.truthy())),
            Operator::UnOp(UnOp::ArithmeticalNegate) => value.neg(),
            Operator::BinOp(BinOp::And, node) => if value.truthy() { self.eval(node) } else { Ok(value) },
            Operator::BinOp(BinOp::Or, node) => if value.truthy() { Ok(value) } else { self.eval(node) },
            Operator::BinOp(BinOp::Add, node) => value.add(&self.eval(node)?),
            Operator::BinOp(BinOp::Subtract, node) => value.sub(&self.eval(node)?),
            Operator::BinOp(BinOp::Multiply, node) => value.mul(&self.eval(node)?),
            Operator::BinOp(BinOp::Divide, node) => value.div(&self.eval(node)?),
            Operator::BinOp(BinOp::IntegerDivide, node) => value.idiv(self.eval(node)?),
            Operator::BinOp(BinOp::Power, node) => value.pow(&self.eval(node)?),
            Operator::BinOp(BinOp::Less, node) => value.cmp_bool(&self.eval(node)?, Ordering::Less).map(Object::from),
            Operator::BinOp(BinOp::LessEqual, node) => value.cmp_bool(&self.eval(node)?, Ordering::Greater).map(bool::not).map(Object::from),
            Operator::BinOp(BinOp::Greater, node) => value.cmp_bool(&self.eval(node)?, Ordering::Greater).map(Object::from),
            Operator::BinOp(BinOp::GreaterEqual, node) => value.cmp_bool(&self.eval(node)?, Ordering::Less).map(bool::not).map(Object::from),
            Operator::BinOp(BinOp::Equal, node) => Ok(Object::from(value.user_eq(&self.eval(node)?))),
            Operator::BinOp(BinOp::NotEqual, node) => Ok(Object::from(!value.user_eq(&self.eval(node)?))),
            Operator::BinOp(BinOp::Index, node) => value.index(&self.eval(node)?),
            Operator::FunCall(elements) => {
                let mut call_args: List = vec![];
                let mut call_kwargs: Map = Map::new();
                for element in elements {
                    self.fill_args(element, &mut call_args, &mut call_kwargs)?;
                }
                value.call(&call_args, Some(&call_kwargs))
            },
        }
    }

    pub fn eval_file<T: ImportResolver>(&mut self, file: &File, importer: &T) -> Result<Object, Error> {
        let mut ns = self.subtend();
        for statement in &file.statements {
            match statement {
                TopLevel::Import(path, binding) => {
                    let object = importer.resolve(path.as_str())?;
                    ns.bind(binding.as_ref(), object)?;
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
                            let text = val.format()?;
                            rval += &text;
                        }
                    }
                }
                Ok(Object::nat_string(rval))
            },

            Expr::Identifier(name) => self.get(name.as_ref()),

            Expr::List(elements) => {
                let mut values: List = vec![];
                for element in elements {
                    self.fill_list(element.as_ref(), &mut values)?;
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
                    sub.bind(binding.as_ref(), val)?;
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
                Ok(Object::from(Function {
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
    let parent = path.parent().ok_or_else(Error::default)?;
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
