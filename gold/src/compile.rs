use gc::{Trace, Finalize};
use serde::{Serialize, Deserialize};

use crate::ast::{BinOp, Expr, Transform, UnOp};
use crate::error::Error;
use crate::object::Object;
use crate::wrappers::GcCell;


#[derive(Debug, Serialize, Deserialize, Trace, Finalize)]
pub(crate) struct Function {
    pub constants: Vec<Object>,
    pub cells: Vec<GcCell<Object>>,

    #[unsafe_ignore_trace]
    pub code: Vec<Instruction>,
}


#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub(crate) enum Instruction {
    LoadConst(usize),

    // Control flow
    Return,
    CondJump(usize),
    Jump(usize),
    Duplicate,
    Discard,
    Noop,

    // Unary operators
    ArithmeticalNegate,
    LogicalNegate,

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

    // Constructors
    NewList,
    NewMap,
}


pub(crate) struct Compiler {
    constants: Vec<Object>,
    code: Vec<Instruction>,
}

impl Compiler {
    pub fn new() -> Compiler {
        Compiler {
            code: Vec::new(),
            constants: Vec::new(),
         }
    }

    pub fn emit(&mut self, expr: &Expr) -> Result<usize, Error> {
        match expr {
            Expr::Literal(obj) => {
                let index = self.constant(obj.clone());
                self.instruction(Instruction::LoadConst(index));
                Ok(1)
            }

            Expr::Transformed { operand, transform } => {
                let mut len = self.emit(operand)?;
                len += self.emit_transform(transform)?;
                Ok(len)
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
                Ok(1)
            }

            Expr::Map(elements) => {
                self.instruction(Instruction::NewMap);
                Ok(1)
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
                    BinOp::Or | BinOp::And => {}
                    _ => {}
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

    pub fn finalize(mut self) -> Function {
        self.code.push(Instruction::Return);
        Function {
            constants: self.constants,
            cells: Vec::new(),
            code: self.code,
        }
    }
}
