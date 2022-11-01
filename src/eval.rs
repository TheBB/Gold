use std::cmp::Ordering;
use std::ops::Neg;
use std::rc::Rc;

use num_traits::checked_pow;
use rug::Integer;
use rug::ops::Pow;

use crate::ast::*;
use crate::object::{Object, Function, Key, Map, List, Builtin};
use crate::builtins::BUILTINS;


struct Arith<F,G,H,X,Y,Z>
where
    F: Fn(i64, i64) -> Option<X>,
    G: Fn(&Integer, &Integer) -> Y,
    H: Fn(f64, f64) -> Z,
{
    ixi: F,
    bxb: G,
    fxf: H,
}


fn arithmetic_operate<F,G,H,X,Y,Z>(ops: Arith<F,G,H,X,Y,Z>, x: Object, y: Object) -> Result<Object, String>
where
    F: Fn(i64, i64) -> Option<X>,
    G: Fn(&Integer, &Integer) -> Y,
    H: Fn(f64, f64) -> Z,
    Object: From<X>,
    Object: From<Y>,
    Object: From<Z>,
{
    let Arith { ixi, bxb, fxf } = ops;

    match (x, y) {
        (Object::Integer(xx), Object::Integer(yy)) => Ok(
            ixi(xx, yy).map(Object::from).unwrap_or_else(
                || Object::from(bxb(&Integer::from(xx), &Integer::from(yy))).numeric_normalize()
            )
        ),

        (Object::Integer(xx), Object::BigInteger(yy)) => Ok(Object::from(bxb(&Integer::from(xx), &yy)).numeric_normalize()),
        (Object::BigInteger(xx), Object::Integer(yy)) => Ok(Object::from(bxb(&xx, &Integer::from(yy))).numeric_normalize()),
        (Object::BigInteger(xx), Object::BigInteger(yy)) => Ok(Object::from(bxb(&xx, &yy)).numeric_normalize()),

        (Object::Float(xx), Object::Float(yy)) => Ok(Object::from(fxf(xx, yy))),
        (Object::Integer(xx), Object::Float(yy)) => Ok(Object::from(fxf(xx as f64, yy))),
        (Object::Float(xx), Object::Integer(yy)) => Ok(Object::from(fxf(xx, yy as f64))),

        (Object::Float(xx), Object::BigInteger(yy)) => Ok(Object::from(fxf(xx, yy.to_f64()))),
        (Object::BigInteger(xx), Object::Float(yy)) => Ok(Object::from(fxf(xx.to_f64(), yy))),

        _ => Err("unsupported types for arithmetic".to_string()),
    }
}


fn power(x: Object, y: Object) -> Result<Object, String> {
    match (&x, &y) {
        (Object::Integer(x), Object::Integer(y)) if *y >= 0 => {
            let yy: u32 = (*y).try_into().or_else(|_| Err("unable to convert exponent"))?;
            Ok(checked_pow(*x, yy as usize).map(Object::from).unwrap_or_else(
                || Object::from(Integer::from(*x).pow(yy))
            ))
        },

        (Object::BigInteger(x), Object::Integer(y)) if *y >= 0 => {
            let yy: u32 = (*y).try_into().or_else(|_| Err("unable to convert exponent"))?;
            Ok(Object::from(Integer::from(x.as_ref().pow(yy))))
        },

        _ => {
            let xx: f64 = x.try_into().map_err(|_| "wrong type for power".to_string())?;
            let yy: f64 = y.try_into().map_err(|_| "wrong type for power".to_string())?;
            Ok(Object::from(xx.powf(yy)))
        },
    }
}


enum Namespace<'a> {
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

    pub fn set(&mut self, key: &Key, value: Object) -> Result<(), String> {
        if let Namespace::Mutable { names, .. } = self {
            names.insert(key.clone(), value);
            Ok(())
        } else {
            Err("setting in frozen namespace".to_string())
        }
    }

    pub fn get(&self, key: &Key) -> Result<Object, String> {
        match self {
            Namespace::Empty => BUILTINS.get(key.as_str()).map(
                |x| Object::Builtin(Builtin {
                    name: key.clone(),
                    func: *x,
                })
            ).ok_or_else(|| format!("unknown name {}", key)),
            // match key.as_str() {
            //     "bool" => Ok(Object::Builtin(builtins::to_bool)),
            //     "float" => Ok(Object::Builtin(builtins::to_float)),
            //     "int" => Ok(Object::Builtin(builtins::to_int)),
            //     "str" => Ok(Object::Builtin(builtins::to_str)),
            //     "len" => Ok(Object::Builtin(builtins::len)),
            //     "range" => Ok(Object::Builtin(builtins::range)),
            //     _ => Err(format!("unknown name {}", key)),
            // },
            Namespace::Frozen(names) => names.get(key).map(Object::clone).ok_or_else(|| format!("unknown name {}", key)),
            Namespace::Mutable { names, prev } => names.get(key).map(Object::clone).ok_or(()).or_else(|_| prev.get(key))
        }
    }

    fn bind(&mut self, binding: &Binding, value: Object) -> Result<(), String> {
        match (binding, value) {
            (Binding::Identifier(key), val) => {
                self.set(key, val)?;
                Ok(())
            },

            (Binding::List(bindings), Object::List(values)) => {
                let mut value_iter = values.iter();
                let nslurp = values.len() as i64 - bindings.len() as i64 + 1;

                for binding_element in bindings {
                    match binding_element {
                        ListBindingElement::Binding { binding, default } => {
                            let val = value_iter.next()
                                .map(Object::clone)
                                .ok_or_else(|| "not enough elements".to_string())
                                .or_else(|_| {
                                    default.as_ref()
                                        .ok_or_else(|| "not enough elements, missing default".to_string())
                                        .and_then(|node| self.eval(&node))
                                })?;

                            self.bind(binding, val)?;
                        },

                        ListBindingElement::Slurp => {
                            for _ in 0..nslurp {
                                if let None = value_iter.next() {
                                    return Err("??".to_string())
                                }
                            }
                        },

                        ListBindingElement::SlurpTo(name) => {
                            let mut values: List = vec![];
                            for _ in 0..nslurp {
                                match value_iter.next() {
                                    None => return Err("???".to_string()),
                                    Some(val) => values.push(val.clone()),
                                }
                            }
                            self.set(name, Object::List(Rc::new(values)))?;
                        }
                    }
                }

                if let Some(_) = value_iter.next() {
                    Err("unhandled elements in list".to_string())
                } else {
                    Ok(())
                }
            },

            (Binding::Map(bindings), Object::Map(values)) => {
                let mut slurp_target: Option<&Key> = None;

                for binding_element in bindings {
                    match binding_element {
                        MapBindingElement::Binding { key, binding, default } => {
                            let val = values.get(key)
                                .map(Object::clone)
                                .ok_or_else(|| "zomg".to_string())
                                .or_else(|_| {
                                    default.as_ref()
                                        .ok_or_else(|| "?????".to_string())
                                        .and_then(|node| self.eval(&node))
                                })?;

                            self.bind(binding, val)?;
                        },
                        MapBindingElement::SlurpTo(target) => {
                            slurp_target = Some(target);
                        },
                    }
                }

                if let Some(target) = slurp_target {
                    let mut values: Map = values.as_ref().clone();

                    for binding_element in bindings {
                        if let MapBindingElement::Binding { key, .. } = binding_element {
                            values.remove(key);
                        }
                    }

                    self.set(target, Object::Map(Rc::new(values)))?;
                }

                Ok(())
            },

            _ => {
                Err("unsupported binding".to_string())
            },
        }
    }

    fn fill_list(&self, element: &ListElement, values: &mut List) -> Result<(), String> {
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
                    Err("splatting non-list".to_string())
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
                if let Object::List(from_values) = self.eval(iterable)? {
                    let mut sub = self.subtend();
                    for entry in &*from_values {
                        sub.bind(binding, entry.clone())?;
                        sub.fill_list(element.as_ref(), values)?;
                    }
                    Ok(())
                } else {
                    Err("iterating over non-list".to_string())
                }
            }
        }
    }

    fn fill_map(&self, element: &MapElement, values: &mut Map) -> Result<(), String> {
        match element {
            MapElement::Singleton { key, value } => {
                if let Object::String(k) = self.eval(key)? {
                    let v = self.eval(value)?;
                    values.insert(k, v);
                    Ok(())
                } else {
                    Err("key not a string".to_string())
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
                    Err("splatting a non-map".to_string())
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
                        sub.bind(binding, entry.clone())?;
                        sub.fill_map(element.as_ref(), values)?;
                    }
                    Ok(())
                } else {
                    Err("iterating over non-list".to_string())
                }
            }
        }
    }

    fn fill_args(&self, element: &ArgElement, args: &mut List, kwargs: &mut Map) -> Result<(), String> {
        match element {
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
                    _ => Err("splatting non-list, non-map".to_string()),
                }
            },

            ArgElement::Keyword(key, value) => {
                kwargs.insert(key.clone(), self.eval(value)?);
                Ok(())
            }
        }
    }

    fn operate(&self, operator: &Operator, value: Object) -> Result<Object, String> {
        let add = Arith {
            ixi: i64::checked_add,
            bxb: |x,y| Integer::from(x + y),
            fxf: |x,y| x + y,
        };
        let sub = Arith {
            ixi: i64::checked_sub,
            bxb: |x,y| Integer::from(x - y),
            fxf: |x,y| x - y,
        };
        let mul = Arith {
            ixi: i64::checked_mul,
            bxb: |x,y| Integer::from(x * y),
            fxf: |x,y| x * y,
        };
        let div = Arith {
            ixi: |x,y| Some((x as f64) / (y as f64)),
            bxb: |x,y| x.to_f64() / y.to_f64(),
            fxf: |x,y| x / y,
        };
        let idiv = Arith {
            ixi: i64::checked_div,
            bxb: |x,y| Integer::from(x / y),
            fxf: |x,y| (x / y).floor() as f64,
        };

        match operator {
            Operator::UnOp(op) => match op {
                UnOp::Passthrough => Ok(value),
                UnOp::LogicalNegate => Ok(Object::Boolean(!value.truthy())),
                UnOp::ArithmeticalNegate => match value {
                    Object::Integer(x) => Ok(Object::Integer(-x)),
                    Object::BigInteger(x) => Ok(Object::from((*x).clone().neg())),
                    Object::Float(x) => Ok(Object::Float(-x)),
                    _ => Err("type mismatch".to_string()),
                },
            }
            Operator::BinOp(BinOp::And, node) => if value.truthy() { self.eval(node) } else { Ok(value) },
            Operator::BinOp(BinOp::Or, node) => if value.truthy() { Ok(value) } else { self.eval(node) },
            Operator::BinOp(op, node) => {
                let other = self.eval(node)?;
                match (op, &value, &other) {
                    (BinOp::Index, Object::List(x), Object::Integer(y)) => Ok(x[*y as usize].clone()),
                    (BinOp::Index, Object::Map(x), Object::String(y)) => x.get(y).ok_or_else(|| "unknown key".to_string()).map(Object::clone),
                    (BinOp::Add, Object::List(x), Object::List(y)) => Ok(
                        Object::List(Rc::new(x.iter().chain(y.iter()).map(Object::clone).collect()))
                    ),
                    (BinOp::Add, _, _) => arithmetic_operate(add, value, other),
                    (BinOp::Subtract, _, _) => arithmetic_operate(sub, value, other),
                    (BinOp::Multiply, _, _) => arithmetic_operate(mul, value, other),
                    (BinOp::Divide, _, _) => arithmetic_operate(div, value, other),
                    (BinOp::IntegerDivide, _, _) => arithmetic_operate(idiv, value, other),
                    (BinOp::Power, _, _) => power(value, other),
                    (BinOp::Less, _, _) => value.partial_cmp(&other).map(|x| Object::Boolean(x == Ordering::Less)).ok_or_else(|| "err".to_string()),
                    (BinOp::LessEqual, _, _) => value.partial_cmp(&other).map(|x| Object::Boolean(x != Ordering::Greater)).ok_or_else(|| "err".to_string()),
                    (BinOp::Greater, _, _) => value.partial_cmp(&other).map(|x| Object::Boolean(x == Ordering::Greater)).ok_or_else(|| "err".to_string()),
                    (BinOp::GreaterEqual, _, _) => value.partial_cmp(&other).map(|x| Object::Boolean(x != Ordering::Less)).ok_or_else(|| "err".to_string()),
                    (BinOp::Equal, _, _) => Ok(Object::from(value.user_eq(&other))),
                    (BinOp::NotEqual, _, _) => Ok(Object::from(!value.user_eq(&other))),
                    _ => Err("unsupported operator".to_string()),
                }
            },
            Operator::FunCall(elements) => {
                let mut call_args: List = vec![];
                let mut call_kwargs: Map = Map::new();
                for element in elements {
                    self.fill_args(element, &mut call_args, &mut call_kwargs)?;
                }

                match value {
                    Object::Function(func) => {
                        let Function { args, kwargs, closure, expr } = func.as_ref();
                        let ns = Namespace::Frozen(closure);
                        let mut sub = ns.subtend();
                        sub.bind(args, Object::List(Rc::new(call_args)))?;
                        sub.bind(kwargs, Object::Map(Rc::new(call_kwargs)))?;
                        sub.eval(expr)
                    },
                    Object::Builtin(Builtin { func, .. }) => {
                        func(&call_args, &call_kwargs)
                    },
                    _ => Err("calling a non-function".to_string()),
                }
            },
        }
    }

    pub fn eval(&self, node: &AstNode) -> Result<Object, String> {
        match node {
            AstNode::Literal(val) => Ok(val.clone()),

            AstNode::String(elements) => {
                let mut rval = String::new();
                for element in elements {
                    match element {
                        StringElement::Raw(val) => rval += val,
                        StringElement::Interpolate(expr) => {
                            let val = self.eval(expr)?;
                            let text = val.fmt()?;
                            rval += &text;
                        }
                    }
                }
                Ok(Object::string(rval))
            },

            AstNode::Identifier(name) => self.get(name),

            AstNode::List(elements) => {
                let mut values: List = vec![];
                for element in elements {
                    self.fill_list(element, &mut values)?;
                }
                Ok(Object::List(Rc::new(values)))
            },

            AstNode::Map(elements) => {
                let mut values: Map = Map::new();
                for element in elements {
                    self.fill_map(element, &mut values)?;
                }
                Ok(Object::Map(Rc::new(values)))
            }

            AstNode::Let { bindings, expression } => {
                let mut sub = self.subtend();
                for (binding, expr) in bindings {
                    let val = sub.eval(expr)?;
                    sub.bind(binding, val)?;
                }
                sub.eval(expression)
            },

            AstNode::Operator { operand, operator } => {
                let x = self.eval(operand)?;
                self.operate(operator, x)
            },

            AstNode::Branch { condition, true_branch, false_branch } => {
                let cond = self.eval(condition)?;
                if cond.truthy() {
                    self.eval(true_branch)
                } else {
                    self.eval(false_branch)
                }
            },

            AstNode::Function { positional, keywords, expression } => {
                let mut closure: Map = Map::new();
                for ident in node.free() {
                    let val = self.get(&ident)?;
                    closure.insert(ident, val);
                }
                Ok(Object::Function(Rc::new(Function {
                    args: positional.clone(),
                    kwargs: keywords.clone(),
                    closure,
                    expr: expression.as_ref().clone(),
                })))
            },
        }
    }
}


pub fn eval(node: &AstNode) -> Result<Object, String> {
    Namespace::Empty.eval(node)
}
