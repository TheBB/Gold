use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use gc::{Trace, Finalize};
use serde::{Serialize, Deserialize};

use crate::ast::{ArgElement, BinOp, Binding, Expr, FormatSpec, ListBinding, ListBindingElement, ListElement, MapBinding, MapBindingElement, MapElement, StringElement, Transform, UnOp};
use crate::error::{Error, Reason};
use crate::object::{Key, Object};
use crate::wrappers::GcCell;


#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub(crate) struct Function {
    pub constants: Vec<Object>,
    pub functions: Vec<Function>,

    #[unsafe_ignore_trace]
    pub code: Vec<Instruction>,

    #[unsafe_ignore_trace]
    pub fmt_specs: Vec<FormatSpec>,

    pub num_locals: usize,
}


#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub(crate) enum Instruction {
    // Loading
    LoadConst(usize),
    LoadLocal(usize),
    LoadFunc(usize),

    // Storing
    StoreLocal(usize),

    // Control flow
    Return,
    CondJump(usize),
    Jump(usize),
    Duplicate,
    Discard,
    DiscardMany(usize),
    Interchange,
    Call,
    Noop,

    // Asserts
    ListMinLength(usize),
    ListMinMaxLength(usize, usize),

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
    DelKeyIfExists(Key),

    // Shortcuts for internal use
    IntIndexL(usize),
    IntIndexLAndJump { index: usize, jump: usize },
    IntIndexFromEnd { index: usize, root_front: usize, root_back: usize },
    IntIndexFromEndAndJump { index: usize, root_front: usize, root_back: usize, jump: usize },
    IntSlice { start: usize, from_end: usize },
    IntIndexM(Key),
    IntIndexMAndJump { key: Key, jump: usize },
    IntPushToKwargs(Key),
    IntArgSplat,
}



pub(crate) struct Compiler {
    constants: Vec<Object>,
    funcs: Vec<Function>,
    fmt_specs: Vec<FormatSpec>,

    code: Vec<Instruction>,

    names: Vec<(usize, HashMap<Key, usize>)>,
    num_slots: usize,
}

impl Compiler {
    pub fn new() -> Compiler {
        Compiler {
            constants: Vec::new(),
            funcs: Vec::new(),
            code: Vec::new(),
            fmt_specs: Vec::new(),
            names: vec![(0, HashMap::new())],
            num_slots: 0,
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
                self.instruction(Instruction::LoadLocal(self.index_of_name(key)?));
                Ok(1)
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
                self.pop_namespace();
                Ok(len)
            }

            Expr::Function { positional, keywords, expression } => {
                let mut compiler = Compiler::new();
                compiler.emit_list_binding(positional)?;
                compiler.instruction(Instruction::Discard);
                if let Some(kw) = keywords {
                    compiler.emit_map_binding(kw)?;
                }
                compiler.instruction(Instruction::Discard);
                compiler.emit(expression)?;
                let func = compiler.finalize();

                let index = self.function(func);
                self.instruction(Instruction::LoadFunc(index));
                Ok(1)
            }

            _ => { Ok(0) }
        }
    }

    fn emit_binding(&mut self, binding: &Binding) -> Result<usize, Error> {
        match binding {
            Binding::Identifier(key) => {
                let index = self.bind_name(key);
                self.instruction(Instruction::StoreLocal(index));
                Ok(1)
            }

            Binding::List(elements) => {
                let len = self.emit_list_binding(elements.as_ref())?;
                self.instruction(Instruction::Discard);
                Ok(len + 1)
            }

            Binding::Map(elements) => {
                let len = self.emit_map_binding(elements.as_ref())?;
                self.instruction(Instruction::Discard);
                Ok(len + 1)
            }
        }
    }

    fn emit_list_binding(&mut self, binding: &ListBinding) -> Result<usize, Error> {
        let mut len = 0;
        let solution = binding.solution();

        if solution.slurp.is_some() {
            self.instruction(Instruction::ListMinLength(solution.num_front + solution.num_back));
            len += 1;
        } else {
            self.instruction(Instruction::ListMinMaxLength(solution.num_front, solution.num_front + solution.def_front));
            len += 1;
        }

        if let Some(Some(key)) = solution.slurp {
            self.instruction(Instruction::IntSlice {
                start: solution.num_front + solution.def_front,
                from_end: solution.num_back + solution.def_back,
            });
            let index = self.bind_name(&key);
            self.instruction(Instruction::StoreLocal(index));
            len += 2;
        }

        for (i, element) in solution.front.iter().enumerate() {
            match element.as_ref() {
                ListBindingElement::Binding { binding, default } => {
                    if let Some(d) = default {
                        let index = self.instruction(Instruction::Noop);
                        let default_len = self.emit(d.as_ref())?;
                        self.code[index] = Instruction::IntIndexLAndJump { index: i, jump: default_len };
                        len += default_len + 1;
                    } else {
                        self.instruction(Instruction::IntIndexL(i));
                        len += 1;
                    }
                    len += self.emit_binding(binding)?;
                }

                _ => {}
            }
        }

        for (i, element) in solution.back.iter().enumerate() {
            match element.as_ref() {
                ListBindingElement::Binding { binding, default } => {
                    if let Some(d) = default {
                        let index = self.instruction(Instruction::Noop);
                        let default_len = self.emit(d.as_ref())?;
                        self.code[index] = Instruction::IntIndexFromEndAndJump {
                            index: i,
                            root_front: solution.num_front + solution.def_front,
                            root_back: solution.num_back + solution.def_back,
                            jump: default_len,
                        };
                        len += default_len + 1;
                    } else {
                        self.instruction(Instruction::IntIndexFromEnd {
                            index: i,
                            root_front: solution.num_front + solution.def_front,
                            root_back: solution.num_back + solution.def_back,
                        });
                        len += 1;
                    }
                    len += self.emit_binding(binding)?;
                }

                _ => {}
            }
        }

        Ok(len)
    }

    fn emit_map_binding(&mut self, binding: &MapBinding) -> Result<usize, Error> {
        let mut len = 0;

        for element in binding.0.iter() {
            match element.as_ref() {
                MapBindingElement::Binding { key, binding, default } => {
                    if let Some(d) = default {
                        let index = self.instruction(Instruction::Noop);
                        let default_len = self.emit(d.as_ref())?;
                        self.code[index] = Instruction::IntIndexMAndJump {
                            key: *key.as_ref(),
                            jump: default_len,
                        };
                        len += default_len + 1;
                    } else {
                        self.instruction(Instruction::IntIndexM(*key.as_ref()));
                    }
                    len += self.emit_binding(binding)?;
                }

                MapBindingElement::SlurpTo(key) => {
                    self.instruction(Instruction::Duplicate);
                    len += 1;

                    for element in binding.0.iter() {
                        if let MapBindingElement::Binding { key, .. } = element.as_ref() {
                            self.instruction(Instruction::DelKeyIfExists(*key.as_ref()));
                            len += 1;
                        }
                    }

                    let index = self.bind_name(&key);
                    self.instruction(Instruction::StoreLocal(index));
                    len += 1;
                }
            }
        }

        Ok(len)
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

            Transform::FunCall(args) => {
                let mut len = 0;
                self.instruction(Instruction::NewMap);
                self.instruction(Instruction::NewList);

                for arg in args.iter() {
                    len += self.emit_arg_element(arg)?;
                }

                self.instruction(Instruction::Call);
                Ok(len + 3)
            }
        }
    }

    fn emit_arg_element(&mut self, arg: &ArgElement) -> Result<usize, Error> {
        match arg {
            ArgElement::Singleton(expr) => {
                let len = self.emit(expr)?;
                self.instruction(Instruction::PushToList);
                Ok(len + 1)
            }

            ArgElement::Keyword(key, expr) => {
                let len = self.emit(expr)?;
                self.instruction(Instruction::IntPushToKwargs(**key));
                Ok(len + 1)
            }

            ArgElement::Splat(expr) => {
                let len = self.emit(expr)?;
                self.instruction(Instruction::IntArgSplat);
                Ok(len + 1)
            }
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

    fn function(&mut self, function: Function) -> usize {
        let r = self.funcs.len();
        self.funcs.push(function);
        r
    }

    fn fmt_spec(&mut self, spec: FormatSpec) -> usize {
        let r = self.fmt_specs.len();
        self.fmt_specs.push(spec);
        r
    }

    fn bind_name(&mut self, name: &Key) -> usize {
        let (count, names) = self.names.last_mut().unwrap();
        if names.contains_key(name) {
            names[name]
        } else {
            let r = *count + names.len();
            self.num_slots = (r + 1).max(self.num_slots);
            names.insert(*name, r);
            r
        }
    }

    fn push_namespace(&mut self) {
        if let Some((count, names)) = self.names.last() {
            self.names.push((count + names.len(), HashMap::new()));
        } else {
            self.names.push((0, HashMap::new()));
        }
    }

    fn pop_namespace(&mut self) {
        self.names.pop();
    }

    fn index_of_name(&self, name: &Key) -> Result<usize, Error> {
        for (_, names) in self.names.iter().rev() {
            if names.contains_key(name) {
                return Ok(names[name]);
            }
        }

        Err(Error::new(Reason::None))
    }

    pub fn finalize(mut self) -> Function {
        self.code.push(Instruction::Return);
        Function {
            constants: self.constants,
            functions: self.funcs,
            code: self.code,
            fmt_specs: self.fmt_specs,
            num_locals: self.num_slots,
        }
    }
}
