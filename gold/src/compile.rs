use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use gc::{Trace, Finalize};
use serde::{Serialize, Deserialize};

use crate::ast::{ArgElement, BinOp, Binding, BindingClassifier, BindingMode, BindingShield, Expr, FormatSpec, FreeNames, ListBinding, ListBindingElement, ListElement, MapBinding, MapBindingElement, MapElement, StringElement, Transform, UnOp, Visitable};
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
    pub num_cells: usize,
}


#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub(crate) enum Instruction {
    // Loading
    LoadConst(usize),
    LoadLocal(usize),
    LoadCell(usize),
    LoadEnclosed(usize),
    LoadFunc(usize),

    // Storing
    StoreLocal(usize),
    StoreCell(usize),

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
    PushCellToClosure(usize),

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


#[derive(Debug)]
enum BindingSlot {
    Local(usize),
    Cell(usize),
    Enclosed(usize),
}

#[derive(Debug)]
struct Namespace {
    next_local: usize,
    next_cell: usize,
    next_enclosed: usize,
    types: HashMap<Key, BindingSlot>,
}

impl Namespace {
    pub fn new(parent: Option<&Namespace>) -> Namespace {
        Namespace {
            next_local: parent.as_ref().map(|p| p.next_local).unwrap_or(0),
            next_cell: parent.as_ref().map(|p| p.next_cell).unwrap_or(0),
            next_enclosed: 0,
            types: HashMap::new(),
        }
    }

    pub fn lookup_instruction(&self, key: Key) -> Option<Instruction> {
        match self.types.get(&key) {
            Some(BindingSlot::Local(i)) => Some(Instruction::LoadLocal(*i)),
            Some(BindingSlot::Cell(i)) => Some(Instruction::LoadCell(*i)),
            Some(BindingSlot::Enclosed(i)) => Some(Instruction::LoadEnclosed(*i)),
            None => None,
        }
    }

    pub fn store_instruction(&mut self, key: Key) -> Instruction {
        match self.types.get(&key) {
            Some(BindingSlot::Local(i)) => Instruction::StoreLocal(*i),
            Some(BindingSlot::Cell(i)) => Instruction::StoreCell(*i),
            Some(BindingSlot::Enclosed(_)) => { panic!("storing in an enclosed slot"); },
            None => {
                self.types.insert(key, BindingSlot::Local(self.next_local));
                self.next_local += 1;
                Instruction::StoreLocal(self.next_local - 1)
            },
        }
    }

    pub fn mark_cell(&mut self, key: Key) {
        match self.types.get(&key) {
            Some(BindingSlot::Local(_)) => { panic!("mark as cell but already local"); }
            Some(BindingSlot::Cell(_)) => { }
            Some(BindingSlot::Enclosed(_)) => { panic!("maring an enclosed slot as a cell"); }
            None => {
                self.types.insert(key, BindingSlot::Cell(self.next_cell));
                self.next_cell += 1;
            }
        }
    }

    pub fn require_enclosed(&mut self, key: Key) {
        match self.types.get(&key) {
            Some(BindingSlot::Enclosed(_)) => { }
            Some(_) => { panic!("marking as enclosed a binding that already exists"); }
            None => {
                self.types.insert(key, BindingSlot::Enclosed(self.next_enclosed));
                self.next_enclosed += 1;
            }
        }
    }
}


struct NamespaceStack {
    namespaces: Vec<Namespace>,
}

impl NamespaceStack {
    pub fn new() -> NamespaceStack {
        NamespaceStack { namespaces: vec![Namespace::new(None)] }
    }

    pub fn push(&mut self) {
        self.namespaces.push(Namespace::new(self.namespaces.last()))
    }

    pub fn pop(&mut self) {
        self.namespaces.pop();
    }

    pub fn lookup_instruction(&self, key: Key) -> Option<Instruction> {
        for namespace in self.namespaces.iter().rev() {
            if let Some(instruction) = namespace.lookup_instruction(key) {
                return Some(instruction);
            }
        }
        None
    }

    pub fn store_instruction(&mut self, key: Key) -> Instruction {
        self.namespaces.last_mut().unwrap().store_instruction(key)
    }

    pub fn mark_cell(&mut self, key: Key) {
        self.namespaces.last_mut().unwrap().mark_cell(key);
    }

    pub fn require_enclosed(&mut self, key: Key) {
        self.namespaces.last_mut().unwrap().require_enclosed(key);
    }
}


pub(crate) struct Compiler {
    constants: Vec<Object>,
    funcs: Vec<Function>,
    fmt_specs: Vec<FormatSpec>,

    code: Vec<Instruction>,

    names: NamespaceStack,

    num_locals: usize,
    num_cells: usize,
}

impl Compiler {
    pub fn new() -> Compiler {
        Compiler {
            constants: Vec::new(),
            funcs: Vec::new(),
            fmt_specs: Vec::new(),
            code: Vec::new(),
            names: NamespaceStack::new(),
            num_locals: 0,
            num_cells: 0,
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
                if let Some(instruction) = self.names.lookup_instruction(**key) {
                    self.instruction(instruction);
                    Ok(1)
                } else {
                    eprintln!("failed to look up {:?}", **key);
                    return Err(Error::new(Reason::None));
                }
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
                self.names.push();

                let mut classifier = BindingClassifier::new();
                for (binding, expr) in bindings {
                    expr.visit(&mut classifier);
                    binding.visit(&mut classifier);
                }
                expression.visit(&mut classifier);

                for key in classifier.names_with_mode(BindingMode::Cell) {
                    println!("marking {:?} as cell in let-binding", key);
                    self.names.mark_cell(key);
                }

                let mut len = 0;
                for (binding, expr) in bindings {
                    len += self.emit(expr)?;
                    len += self.emit_binding(binding)?;
                }

                len += self.emit(expression)?;
                self.names.pop();
                Ok(len)
            }

            Expr::Function { positional, keywords, expression } => {
                let load_index = self.instruction(Instruction::Noop);
                let mut len = 1;

                let mut compiler = Compiler::new();

                let mut name_collection = FreeNames::new();
                let mut shield = BindingShield::new(&mut name_collection);
                positional.visit(&mut shield);
                keywords.as_ref().map(|kw| kw.visit(&mut shield));
                expression.visit(&mut shield);

                println!("compiling a function");

                for name in name_collection.free_names() {
                    compiler.require_enclosed(*name);
                    println!("{:?}", self.names.lookup_instruction(*name));
                    if let Some(Instruction::LoadCell(i)) = self.names.lookup_instruction(*name) {
                        self.instruction(Instruction::PushCellToClosure(i));
                        len += 2;
                    } else {
                        panic!("failed to look up name that must be provided to closure: {:?}", name);
                    }
                }

                let mut new_name_collection = FreeNames::new();
                expression.visit(&mut new_name_collection);

                for name in new_name_collection.captured_names() {
                    println!("marking as captured: {:?}", name);
                    compiler.names.mark_cell(name);
                }

                compiler.emit_list_binding(positional)?;
                compiler.instruction(Instruction::Discard);
                if let Some(kw) = keywords {
                    compiler.emit_map_binding(kw)?;
                }
                compiler.instruction(Instruction::Discard);
                compiler.emit(expression)?;

                let func = compiler.finalize();

                let index = self.function(func);
                self.code[load_index] = Instruction::LoadFunc(index);
                println!("compiled a function");
                Ok(len)
            }

            _ => { Ok(0) }
        }
    }

    fn emit_binding(&mut self, binding: &Binding) -> Result<usize, Error> {
        match binding {
            Binding::Identifier(key) => {
                let instruction = self.names.store_instruction(**key);
                self.instruction(instruction);
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
            let instruction = self.names.store_instruction(key);
            self.instruction(instruction);
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

                    let instruction = self.names.store_instruction(**key);
                    self.instruction(instruction);

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

            ListElement::Cond { condition, element } => {
                let condition_len = self.emit(condition)?;
                self.instruction(Instruction::LogicalNegate);
                let index = self.instruction(Instruction::Noop);
                let element_len = self.emit_list_element(element)?;
                self.code[index] = Instruction::CondJump(element_len);
                Ok(condition_len + element_len + 2)
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

            MapElement::Cond { condition, element } => {
                let condition_len = self.emit(condition)?;
                self.instruction(Instruction::LogicalNegate);
                let index = self.instruction(Instruction::Noop);
                let element_len = self.emit_map_element(element)?;
                self.code[index] = Instruction::CondJump(element_len);
                Ok(condition_len + element_len + 2)
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

        match instruction {
            Instruction::StoreLocal(i) => { self.num_locals = self.num_locals.max(i + 1); }
            Instruction::LoadLocal(i) => { self.num_locals = self.num_locals.max(i + 1); }
            Instruction::StoreCell(i) => { self.num_cells = self.num_cells.max(i + 1); }
            Instruction::LoadCell(i) => { self.num_cells = self.num_cells.max(i + 1); }
            _ => { }
        }

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

    // fn bind_name(&mut self, name: &Key) -> usize {
    //     let (count, names) = self.names.last_mut().unwrap();
    //     if names.contains_key(name) {
    //         names[name]
    //     } else {
    //         let r = *count + names.len();
    //         self.num_slots = (r + 1).max(self.num_slots);
    //         names.insert(*name, r);
    //         r
    //     }
    // }

    // fn push_namespace(&mut self) {
    //     if let Some((count, names)) = self.names.last() {
    //         self.names.push((count + names.len(), HashMap::new()));
    //     } else {
    //         self.names.push((0, HashMap::new()));
    //     }
    // }

    // fn pop_namespace(&mut self) {
    //     self.names.pop();
    // }

    // fn index_of_name(&self, name: &Key) -> Option<usize> {
    //     for (_, names) in self.names.iter().rev() {
    //         if names.contains_key(name) {
    //             return Some(names[name]);
    //         }
    //     }

    //     None
    // }

    // fn index_of_cell(&self, name: &Key) -> Option<usize> {
    //     self.cells.get(name).copied()
    // }

    pub fn require_enclosed(&mut self, key: Key) {
        self.names.require_enclosed(key);
    }

    pub fn finalize(mut self) -> Function {
        self.code.push(Instruction::Return);
        Function {
            functions: self.funcs,
            constants: self.constants,
            code: self.code,
            fmt_specs: self.fmt_specs,
            num_locals: self.num_locals,
            num_cells: self.num_cells,
        }
    }
}
