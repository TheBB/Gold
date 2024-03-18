use std::collections::{HashMap, HashSet};

use gc::{Trace, Finalize};
use serde::{Serialize, Deserialize};

use crate::ast::{BinOp, Binding, Expr, FormatSpec, ListElement, MapElement, StringElement, Transform, UnOp};
use crate::error::{Error, Reason};
use crate::object::{Key, Object};
use crate::wrappers::GcCell;


#[derive(Debug, Serialize, Deserialize, Trace, Finalize)]
pub(crate) struct Function {
    pub constants: Vec<Object>,
    pub cells: Vec<GcCell<Object>>,

    #[unsafe_ignore_trace]
    pub code: Vec<Instruction>,

    #[unsafe_ignore_trace]
    pub fmt_specs: Vec<FormatSpec>,
}


#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub(crate) enum Instruction {
    LoadConst(usize),

    // Control flow
    Return,
    CondJump(usize),
    Jump(usize),
    Duplicate,
    DuplicateIndex(usize),
    Discard,
    DiscardMany(usize),
    Noop,

    // Unary operators
    ArithmeticalNegate,
    LogicalNegate,
    Format(usize),

    // Binary mathematical operators
    Add,
    Subtract,
    Multiply,
    IntegerDivide,
    Divide,
    Power,

    // Binary comparison operators
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual,
    Contains,

    // Other operators
    Index,

    // Constructors
    NewList,
    NewMap,

    // Mutability
    PushToList,
    PushToMap,
    SplatToCollection,
}


pub(crate) struct Compiler {
    constants: Vec<Object>,
    code: Vec<Instruction>,
    fmt_specs: Vec<FormatSpec>,

    names: Vec<(usize, HashMap<Key, usize>)>,
}

impl Compiler {
    pub fn new() -> Compiler {
        Compiler {
            code: Vec::new(),
            constants: Vec::new(),
            fmt_specs: Vec::new(),
            names: Vec::new(),
         }
    }

    pub fn emit(&mut self, expr: &Expr) -> Result<usize, Error> {
        match expr {
            Expr::Literal(obj) => {
                let index = self.constant(obj.clone());
                self.instruction(Instruction::LoadConst(index));
                Ok(1)
            }

            Expr::Identifier(key) => {
                for (_, ns) in self.names.iter().rev() {
                    if ns.contains_key(key) {
                        let index = ns[key];
                        self.instruction(Instruction::DuplicateIndex(index));
                        return Ok(1)
                    }
                }
                Err(Error::new(Reason::None))
            }

            Expr::Transformed { operand, transform } => {
                let mut len = self.emit(operand)?;
                len += self.emit_transform(transform)?;
                Ok(len)
            }

            Expr::String(elements) => {
                let index = self.constant(Object::str(""));
                self.instruction(Instruction::LoadConst(index));

                let mut len = 0;
                for element in elements {
                    len += self.emit_string_element(element)?;
                }
                Ok(len + 1)
            }

            Expr::Branch { condition, true_branch, false_branch } => {
                let cond_len = self.emit(condition)?;
                let cjump_index = self.instruction(Instruction::Noop);
                let false_len = self.emit(false_branch)?;
                let jump_index = self.instruction(Instruction::Noop);
                let true_len = self.emit(true_branch)?;

                self.code[cjump_index] = Instruction::CondJump(false_len + 1);
                self.code[jump_index] = Instruction::Jump(true_len);

                Ok(cond_len + false_len + true_len + 2)
            }

            Expr::List(elements) => {
                self.instruction(Instruction::NewList);

                let mut len = 0;
                for element in elements {
                    len += self.emit_list_element(element)?;
                }
                Ok(len + 1)
            }

            Expr::Map(elements) => {
                self.instruction(Instruction::NewMap);

                let mut len = 0;
                for element in elements {
                    len += self.emit_map_element(element)?;
                }
                Ok(len + 1)
            }

            Expr::Let { bindings, expression } => {
                self.push_namespace();

                let mut len = 0;
                for (binding, expr) in bindings {
                    len += self.emit(expr)?;
                    len += self.emit_binding(binding)?;
                }

                len += self.emit(expression)?;
                len += self.pop_namespace();
                Ok(len)
            }

            _ => { Ok(0) }
        }
    }

    fn emit_binding(&mut self, binding: &Binding) -> Result<usize, Error> {
        match binding {
            Binding::Identifier(key) => {
                self.bind_name(**key);
                Ok(0)
            }

            _ => { Ok(0) }
        }
    }

    fn emit_string_element(&mut self, element: &StringElement) -> Result<usize, Error> {
        match element {
            StringElement::Raw(expr) => {
                let index = self.constant(Object::str(expr.as_ref()));
                self.instruction(Instruction::LoadConst(index));
                self.instruction(Instruction::Add);
                Ok(2)
            }

            StringElement::Interpolate(expr, spec) => {
                let len = self.emit(expr)?;
                let index = self.fmt_spec(spec.unwrap_or_default());
                self.instruction(Instruction::Format(index));
                self.instruction(Instruction::Add);
                Ok(len + 2)
            }
        }
    }

    fn emit_list_element(&mut self, element: &ListElement) -> Result<usize, Error> {
        match element {
            ListElement::Singleton(expr) => {
                let len = self.emit(expr)?;
                self.instruction(Instruction::PushToList);
                Ok(len + 1)
            }

            ListElement::Splat(expr) => {
                let len = self.emit(expr)?;
                self.instruction(Instruction::SplatToCollection);
                Ok(len + 1)
            }

            _ => { Ok(0) }
        }
    }

    fn emit_map_element(&mut self, element: &MapElement) -> Result<usize, Error> {
        match element {
            MapElement::Singleton { key, value } => {
                let mut len = self.emit(key)?;
                len += self.emit(value)?;
                self.instruction(Instruction::PushToMap);
                Ok(len + 1)
            }

            MapElement::Splat(expr) => {
                let len = self.emit(expr)?;
                self.instruction(Instruction::SplatToCollection);
                Ok(len + 1)
            }

            _ => { Ok(0) }
        }
    }

    fn emit_transform(&mut self, transform: &Transform) -> Result<usize, Error> {
        match transform {
            Transform::UnOp(op) => match op.as_ref() {
                UnOp::Passthrough => { Ok(0) },
                UnOp::ArithmeticalNegate => { self.code.push(Instruction::ArithmeticalNegate); Ok(1) }
                UnOp::LogicalNegate => { self.code.push(Instruction::LogicalNegate); Ok(1) }
            }

            Transform::BinOp(operator, operand) => {
                match operator.as_ref() {
                    BinOp::Or => {
                        self.instruction(Instruction::Duplicate);
                        let cjump_index = self.instruction(Instruction::Noop);
                        self.instruction(Instruction::Discard);
                        let false_len = self.emit(operand)?;
                        self.code[cjump_index] = Instruction::CondJump(false_len + 1);
                        return Ok(false_len + 3);
                    }
                    BinOp::And => {
                        self.instruction(Instruction::Duplicate);
                        self.instruction(Instruction::CondJump(1));
                        let jump_index = self.instruction(Instruction::Noop);
                        self.instruction(Instruction::Discard);
                        let true_len = self.emit(operand)?;
                        self.code[jump_index] = Instruction::Jump(true_len + 1);
                        return Ok(true_len + 4);
                    }
                    _ => {}
                }

                let len = self.emit(operand.as_ref())?;
                match operator.as_ref() {
                    BinOp::Power => { self.code.push(Instruction::Power); }
                    BinOp::Multiply => { self.code.push(Instruction::Multiply); }
                    BinOp::IntegerDivide => { self.code.push(Instruction::IntegerDivide); }
                    BinOp::Divide => { self.code.push(Instruction::Divide); }
                    BinOp::Add => { self.code.push(Instruction::Add); }
                    BinOp::Subtract => { self.code.push(Instruction::Subtract); }
                    BinOp::Less => { self.code.push(Instruction::Less); }
                    BinOp::Greater => { self.code.push(Instruction::Greater); }
                    BinOp::LessEqual => { self.code.push(Instruction::LessEqual); }
                    BinOp::GreaterEqual => { self.code.push(Instruction::GreaterEqual); }
                    BinOp::Equal => { self.code.push(Instruction::Equal); }
                    BinOp::NotEqual => { self.code.push(Instruction::NotEqual); }
                    BinOp::Contains => { self.code.push(Instruction::Contains); }
                    BinOp::Index => { self.code.push(Instruction::Index); }
                    BinOp::Or | BinOp::And => {}
                }

                Ok(len + 1)
            }

            _ => { Ok(0) }
        }
    }

    fn instruction(&mut self, instruction: Instruction) -> usize {
        let r = self.code.len();
        self.code.push(instruction);
        r
    }

    fn constant(&mut self, constant: Object) -> usize {
        let r = self.constants.len();
        self.constants.push(constant);
        r
    }

    fn fmt_spec(&mut self, spec: FormatSpec) -> usize {
        let r = self.fmt_specs.len();
        self.fmt_specs.push(spec);
        r
    }

    fn push_namespace(&mut self) {
        if let Some((num_names, names)) = self.names.last() {
            self.names.push((num_names + names.len(), HashMap::new()))
        } else {
            self.names.push((0, HashMap::new()))
        }
    }

    fn pop_namespace(&mut self) -> usize {
        let (len, _) = self.names.pop().unwrap();
        self.instruction(Instruction::DiscardMany(len));
        len
    }

    fn bind_name(&mut self, name: Key) -> usize {
        let (num_names, names) = self.names.last_mut().unwrap();
        let r = *num_names + names.len();
        names.insert(name, r);
        println!("{:?}", self.names);
        r
    }

    pub fn finalize(mut self) -> Function {
        self.code.push(Instruction::Return);
        Function {
            constants: self.constants,
            cells: Vec::new(),
            code: self.code,
            fmt_specs: self.fmt_specs,
        }
    }
}
