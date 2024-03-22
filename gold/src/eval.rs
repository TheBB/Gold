use std::cmp::Ordering;
use std::path::PathBuf;
use std::rc::Rc;

use gc::Gc;

use crate::ast::*;
use crate::builtins::BUILTINS;
use crate::compile::{Function, Instruction};
use crate::error::{BindingType, Error, Reason, TypeMismatch, Unpack};
use crate::wrappers::GcCell;
use crate::{eval_file, eval_raw as eval_str};
use crate::{List, Map, Object, Type};

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
                _ => Err(Error::new(Reason::UnknownImport(path.to_owned()))),
            }
        } else {
            // The custom import resolver has precedence over paths
            if let Some(resolver) = &self.custom {
                if let Some(result) = resolver(path)? {
                    return Ok(result);
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

pub(crate) struct Frame {
    pub function: Function,
    pub stack: Vec<Object>,
    pub locals: Vec<Object>,
    pub cells: Vec<Gc<GcCell<Object>>>,
    pub enclosed: Gc<GcCell<Vec<Gc<GcCell<Object>>>>>,
    pub ip: usize,
}

impl Frame {
    pub fn new(function: Function, enclosed: Gc<GcCell<Vec<Gc<GcCell<Object>>>>>) -> Frame {
        let num_locals = function.num_locals;
        let num_cells = function.num_cells;

        let mut cells = Vec::with_capacity(num_cells);
        for _ in 0..num_cells {
            cells.push(Gc::new(GcCell::new(Object::null())));
        }

        Frame {
            function,
            stack: Vec::new(),
            locals: vec![Object::null(); num_locals],
            cells,
            enclosed,
            ip: 0,
        }
    }

    pub fn next_instruction(&mut self) -> Instruction {
        self.ip += 1;
        self.function.code[self.ip - 1]
    }
}

pub(crate) struct Vm<'a> {
    frames: Vec<Frame>,
    fp: usize,
    importer: &'a ImportConfig,
}

impl<'a> Vm<'a> {
    pub fn new(importer: &'a ImportConfig) -> Self {
        Self {
            frames: vec![],
            fp: 0,
            importer,
        }
    }

    pub fn eval(&mut self, function: Function) -> Result<Object, Error> {
        self.frames
            .push(Frame::new(function, Gc::new(GcCell::new(vec![]))));
        self.fp = 0;
        self.eval_impl()
    }

    pub fn eval_with_args(
        &mut self,
        function: Function,
        enclosed: Gc<GcCell<Vec<Gc<GcCell<Object>>>>>,
        args: &List,
        kwargs: Option<&Map>,
    ) -> Result<Object, Error> {
        self.frames.push(Frame::new(function, enclosed));
        self.fp = 0;
        self.push(
            kwargs
                .cloned()
                .map(Object::map)
                .unwrap_or_else(|| Object::new_map()),
        );
        self.push(Object::list(args.clone()));
        self.eval_impl()
    }

    fn cur_frame(&mut self) -> &mut Frame {
        &mut self.frames[self.fp]
    }

    fn peek_back(&self) -> &Object {
        let stack = &self.frames[self.fp].stack;
        let i = stack.len() - 2;
        stack.get(i).unwrap()
    }

    fn peek(&self) -> &Object {
        self.frames[self.fp].stack.last().unwrap()
    }

    fn pop(&mut self) -> Object {
        self.cur_frame().stack.pop().unwrap()
    }

    fn push(&mut self, obj: Object) {
        self.cur_frame().stack.push(obj)
    }

    fn err(&self) -> Error {
        let mut err = self.frames[self.fp]
            .function
            .trace
            .error(self.frames[self.fp].ip - 1);
        for fp in (0..self.fp).rev() {
            err = err.add_locations(self.frames[fp].function.trace.error(self.frames[fp].ip - 1));
        }
        err
    }

    fn eval_impl(&mut self) -> Result<Object, Error> {
        loop {
            let instruction = self.cur_frame().next_instruction();
            match instruction {
                Instruction::LoadConst(i) => {
                    let obj = self.cur_frame().function.constants[i].clone();
                    self.push(obj);
                }

                Instruction::LoadLocal(i) => {
                    let obj = self.cur_frame().locals[i].clone();
                    self.push(obj);
                }

                Instruction::LoadCell(i) => {
                    let cell = self.cur_frame().cells[i].as_ref();
                    let obj = cell.borrow().clone();
                    self.push(obj);
                }

                Instruction::LoadEnclosed(i) => {
                    let obj = {
                        let e = self.cur_frame().enclosed.as_ref().borrow();
                        let f = e[i].as_ref().borrow();
                        f.clone()
                    };
                    self.push(obj);
                }

                Instruction::LoadFunc(i) => {
                    let func = self.cur_frame().function.functions[i].clone();
                    let obj = Object::closure(func);
                    self.push(obj);
                }

                Instruction::LoadBuiltin(i) => self.push(Object::func(BUILTINS.1[i].clone())),

                Instruction::Import(i) => {
                    let path = self.frames[self.fp].function.import_paths.get(i).unwrap();
                    let object = self
                        .importer
                        .resolve(path.as_ref())
                        .map_err(|e| e.add_locations(self.err()))?;
                    self.push(object);
                }

                Instruction::StoreLocal(i) => {
                    let obj = self.pop();
                    self.cur_frame().locals[i] = obj;
                }

                Instruction::StoreCell(i) => {
                    let obj = self.pop();
                    let cell = self.cur_frame().cells[i].as_ref();
                    *cell.borrow_mut() = obj;
                }

                Instruction::Return => {
                    let obj = self.pop();
                    self.frames.pop();
                    if self.fp == 0 {
                        return Ok(obj);
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

                Instruction::JumpBack(delta) => {
                    self.cur_frame().ip -= delta;
                }

                Instruction::Duplicate => {
                    let obj = self.peek().clone();
                    self.push(obj);
                }

                Instruction::Discard => {
                    self.pop();
                }

                Instruction::DiscardMany(n) => {
                    let obj = self.pop();
                    for _ in 0..n {
                        self.pop();
                    }
                    self.push(obj);
                }

                Instruction::Interchange => {
                    let a = self.pop();
                    let b = self.pop();
                    self.push(a);
                    self.push(b);
                }

                Instruction::Call => {
                    let args = self.pop();
                    let kwargs = self.pop();
                    let func = self.pop();

                    if let Some(f) = func.native_callable() {
                        let x = args.get_list().ok_or_else(|| Error::new(Reason::None))?;
                        let y = kwargs.get_map().ok_or_else(|| Error::new(Reason::None))?;
                        let result = f(&x, Some(&y)).map_err(|e| e.with_locations(self.err()))?;
                        self.push(result);
                    } else if let Some((f, e)) = func.get_closure() {
                        self.frames.push(Frame::new(f.as_ref().clone(), e.clone()));
                        self.fp += 1;
                        self.push(kwargs);
                        self.push(args);
                    } else {
                        return Err(self.err().with_reason(TypeMismatch::Call(func.type_of())))
                    }
                }

                Instruction::Noop => {}

                Instruction::AssertListMinLength(len) => {
                    let obj = self.peek();
                    match obj.get_list() {
                        None => return Err(Error::new(Reason::None)),
                        Some(l) => {
                            if l.len() < len {
                                return Err(Error::new(Reason::None));
                            }
                        }
                    }
                }

                Instruction::AssertListMinMaxLength(min, max) => {
                    let obj = self.peek();
                    match obj.get_list() {
                        None => {
                            return Err(self.err().with_reason(Unpack::TypeMismatch(
                                BindingType::List,
                                obj.type_of(),
                            )))
                        }
                        Some(l) => {
                            if l.len() < min {
                                return Err(self.err().with_reason(Unpack::ListTooShort));
                            }
                            if l.len() > max {
                                return Err(self.err().with_reason(Unpack::ListTooLong));
                            }
                        }
                    }
                }

                Instruction::AssertMap => {
                    let obj = self.peek();
                    match obj.get_map() {
                        None => {
                            return Err(self.err().with_reason(Unpack::TypeMismatch(
                                BindingType::Map,
                                obj.type_of(),
                            )))
                        }
                        Some(_) => {}
                    }
                }

                Instruction::ArithmeticalNegate => {
                    let obj = self.pop();
                    self.push(obj.neg().map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::LogicalNegate => {
                    let obj = self.pop();
                    self.push(Object::bool(!obj.truthy()));
                }

                Instruction::Format(i) => {
                    let obj = self.pop();
                    let result = Object::str(
                        obj.format(&self.cur_frame().function.fmt_specs[i])
                            .map_err(|e| e.with_locations(self.err()))?,
                    );
                    self.push(result);
                }

                Instruction::Add => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.add(&rhs).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::Subtract => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.sub(&rhs).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::Multiply => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.mul(&rhs).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::IntegerDivide => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.idiv(&rhs).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::Divide => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.div(&rhs).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::Power => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.pow(&rhs).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::Less => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Less)
                        .ok_or_else(|| {
                            self.err().with_reason(TypeMismatch::BinOp(
                                lhs.type_of(),
                                rhs.type_of(),
                                BinOp::Less,
                            ))
                        })
                        .map(Object::bool)?;
                    self.push(res);
                }

                Instruction::Greater => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Greater)
                        .ok_or_else(|| {
                            self.err().with_reason(TypeMismatch::BinOp(
                                lhs.type_of(),
                                rhs.type_of(),
                                BinOp::Greater,
                            ))
                        })
                        .map(Object::bool)?;
                    self.push(res);
                }

                Instruction::LessEqual => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Greater)
                        .ok_or_else(|| {
                            self.err().with_reason(TypeMismatch::BinOp(
                                lhs.type_of(),
                                rhs.type_of(),
                                BinOp::LessEqual,
                            ))
                        })
                        .map(|x| Object::bool(!x))?;
                    self.push(res);
                }

                Instruction::GreaterEqual => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    let res = lhs
                        .cmp_bool(&rhs, Ordering::Less)
                        .ok_or_else(|| {
                            self.err().with_reason(TypeMismatch::BinOp(
                                lhs.type_of(),
                                rhs.type_of(),
                                BinOp::GreaterEqual,
                            ))
                        })
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
                    self.push(Object::bool(
                        lhs.contains(&rhs)
                            .map_err(|e| e.with_locations(self.err()))?,
                    ));
                }

                Instruction::Index => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(lhs.index(&rhs).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::NewList => {
                    self.push(Object::new_list());
                }

                Instruction::NewMap => {
                    self.push(Object::new_map());
                }

                Instruction::NewIterator => {
                    let obj = self.pop();
                    self.push(Object::iterator(&obj).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::PushToList => {
                    let obj = self.pop();
                    self.peek().push_to_list(obj)?;
                }

                Instruction::PushToMap => {
                    let value = self.pop();
                    let key = self.pop();
                    self.peek()
                        .push_to_map(key, value)
                        .map_err(|e| e.with_locations(self.err()))?;
                }

                Instruction::SplatToCollection => {
                    let obj = self.pop();
                    self.peek()
                        .splat_into(obj)
                        .map_err(|e| e.with_locations(self.err()))?;
                }

                Instruction::DelKeyIfExists(key) => {
                    let mut l = self
                        .peek()
                        .get_map_mut()
                        .ok_or_else(|| Error::new(Reason::None))?;
                    l.remove(&key);
                }

                Instruction::PushCellToClosure(i) => {
                    let cell = self.cur_frame().cells[i].clone();
                    self.peek().push_to_closure(cell)?;
                }

                Instruction::PushEnclosedToClosure(i) => {
                    let cell = {
                        let cells = self.cur_frame().enclosed.as_ref().borrow();
                        cells[i].clone()
                    };
                    self.peek().push_to_closure(cell)?;
                }

                Instruction::NextOrJump(usize) => {
                    let obj = self.peek().next()?;
                    match obj {
                        None => {
                            self.cur_frame().ip += usize;
                        }
                        Some(x) => {
                            self.push(x);
                        }
                    }
                }

                Instruction::IntIndexL(i) => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_list()
                            .ok_or_else(|| Error::new(Reason::None))?;
                        l.get(i).ok_or_else(|| Error::new(Reason::None))?.clone()
                    };
                    self.push(obj);
                }

                Instruction::IntIndexLAndJump { index, jump } => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_list()
                            .ok_or_else(|| Error::new(Reason::None))?;
                        l.get(index).cloned()
                    };

                    if let Some(x) = obj {
                        self.push(x);
                        self.cur_frame().ip += jump;
                    }
                }

                Instruction::IntIndexFromEnd {
                    index,
                    root_front,
                    root_back,
                } => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_list()
                            .ok_or_else(|| Error::new(Reason::None))?;
                        let i = (l.len() - root_back).max(root_front) + index;
                        l.get(i).ok_or_else(|| Error::new(Reason::None))?.clone()
                    };
                    self.push(obj);
                }

                Instruction::IntIndexFromEndAndJump {
                    index,
                    root_front,
                    root_back,
                    jump,
                } => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_list()
                            .ok_or_else(|| Error::new(Reason::None))?;
                        let root = if root_back > l.len() {
                            root_front
                        } else {
                            (l.len() - root_back).max(root_front)
                        };
                        l.get(root + index).cloned()
                    };

                    if let Some(x) = obj {
                        self.push(x);
                        self.cur_frame().ip += jump;
                    }
                }

                Instruction::IntSlice { start, from_end } => {
                    let obj = self
                        .peek()
                        .get_list()
                        .map(|l| {
                            if from_end > l.len() {
                                return Object::new_list();
                            }
                            let end = l.len() - from_end;
                            if start < end {
                                Object::list(l[start..end].to_vec())
                            } else {
                                Object::new_list()
                            }
                        })
                        .ok_or_else(|| Error::new(Reason::None))?;
                    self.push(obj);
                }

                Instruction::IntIndexM(key) => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_map()
                            .ok_or_else(|| Error::new(Reason::None))?;
                        l.get(&key).ok_or_else(|| self.err())?.clone()
                    };
                    self.push(obj);
                }

                Instruction::IntIndexMAndJump { key, jump } => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_map()
                            .ok_or_else(|| Error::new(Reason::None))?;
                        l.get(&key).cloned()
                    };

                    if let Some(x) = obj {
                        self.push(x);
                        self.cur_frame().ip += jump;
                    }
                }

                Instruction::IntPushToKwargs(key) => {
                    let value = self.pop();
                    self.peek_back().push_to_map_key(key, value)?;
                }

                Instruction::IntArgSplat => {
                    let value = self.pop();
                    if value.type_of() == Type::List {
                        self.peek().splat_into(value)?;
                    } else if value.type_of() == Type::Map {
                        self.peek_back().splat_into(value)?;
                    } else {
                        return Err(Error::new(TypeMismatch::SplatArg(value.type_of()))
                            .with_locations(self.err()));
                    }
                }
            }
        }
    }
}
