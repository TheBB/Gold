use std::collections::{HashMap, HashSet};

use gc::{Finalize, Trace};
use serde::{Deserialize, Serialize};

use crate::ast::low::{Binding, Expr, Function, ListBinding, ListElement, MapBinding, MapBindingElement, MapElement, StringElement, Transform, ArgElement};
use crate::error::{Action, Error, IntervalTree, Reason, Span, Tagged, Unpack};
use crate::formatting::FormatSpec;
use crate::types::{BinOp, UnOp, Key};
use crate::Object;
use crate::ast::{BindingLoc, SlotCatalog, SlotType};

#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub struct CompiledFunction {
    pub constants: Vec<Object>,
    pub functions: Vec<CompiledFunction>,

    #[unsafe_ignore_trace]
    pub code: Vec<Instruction>,

    #[unsafe_ignore_trace]
    pub fmt_specs: Vec<FormatSpec>,

    #[unsafe_ignore_trace]
    pub import_paths: Vec<String>,

    pub num_locals: usize,
    pub num_cells: usize,

    #[unsafe_ignore_trace]
    pub trace: IntervalTree<usize, (Span, Action), Reason>,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Instruction {
    // Loading
    LoadConst(usize),
    LoadLocal(usize),
    LoadCell(usize),
    LoadEnclosed(usize),
    LoadFunc(usize),
    LoadBuiltin(usize),
    Import(usize),

    // Storing
    StoreLocal(usize),
    StoreCell(usize),

    // Destroying
    DestroyLocal(usize),
    DestroyCell(usize),

    // Control flow
    Return,
    CondJump(usize),
    Jump(usize),
    JumpBack(usize),
    Duplicate,
    Discard,
    DiscardMany(usize),
    Interchange,
    Call,
    Noop,

    // Asserts
    AssertListMinLength(usize),
    AssertListMinMaxLength(usize, usize),
    AssertMap,

    // Unary operators
    ArithmeticalNegate,
    LogicalNegate,
    FormatWithSpec(usize),
    FormatWithDefault,

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
    NewIterator,
    NewString,

    // Mutability
    PushToList,
    PushToMap,
    SplatToCollection,
    DelKeyIfExists(Key),
    PushCellToClosure(usize),
    PushEnclosedToClosure(usize),
    NextOrJump(usize),

    // Shortcuts for internal use
    IntIndexL(usize),
    IntIndexLAndJump {
        index: usize,
        jump: usize,
    },
    IntIndexFromEnd {
        index: usize,
        root_front: usize,
        root_back: usize,
    },
    IntIndexFromEndAndJump {
        index: usize,
        root_front: usize,
        root_back: usize,
        jump: usize,
    },
    IntSlice {
        start: usize,
        from_end: usize,
    },
    IntIndexM(Key),
    IntIndexMAndJump {
        key: Key,
        jump: usize,
    },
    IntPushToKwargs(Key),
    IntArgSplat,
}

#[derive(Debug, Clone)]
enum Slot {
    Local(usize),
    Cell(usize),
}

#[derive(Debug, Clone)]
struct SlotMap {
    catalog: SlotCatalog,
    map: HashMap<usize, Slot>,
    next_local: usize,
    next_cell: usize,
}

impl SlotMap {
    fn new(parent: Option<&SlotMap>, catalog: SlotCatalog) -> Self {
        Self {
            catalog,
            map: HashMap::new(),
            next_local: parent.map(|p| p.next_local).unwrap_or(0),
            next_cell: parent.map(|p| p.next_cell).unwrap_or(0),
        }
    }

    fn load_instruction(&mut self, index: usize) -> Option<Instruction> {
        match self.map.get(&index) {
            Some(Slot::Local(i)) => { return Some(Instruction::LoadLocal(*i)); }
            Some(Slot::Cell(i)) => { return Some(Instruction::LoadCell(*i)); }
            None => {}
        }

        match self.catalog.get(&index) {
            Some(SlotType::Local) => {
                let locnum = self.next_local;
                self.next_local += 1;
                self.map.insert(index, Slot::Local(locnum));
                Some(Instruction::LoadLocal(locnum))
            }
            Some(SlotType::Cell) => {
                let cellnum = self.next_cell;
                self.next_cell += 1;
                self.map.insert(index, Slot::Cell(cellnum));
                Some(Instruction::LoadCell(cellnum))
            }
            None => None,
        }
    }

    fn store_instruction(&mut self, index: usize) -> Option<Instruction> {
        match self.map.get(&index) {
            Some(Slot::Local(i)) => { return Some(Instruction::StoreLocal(*i)); }
            Some(Slot::Cell(i)) => { return Some(Instruction::StoreCell(*i)); }
            None => {}
        }

        match self.catalog.get(&index) {
            Some(SlotType::Local) => {
                let locnum = self.next_local;
                self.next_local += 1;
                self.map.insert(index, Slot::Local(locnum));
                Some(Instruction::StoreLocal(locnum))
            }
            Some(SlotType::Cell) => {
                let cellnum = self.next_cell;
                self.next_cell += 1;
                self.map.insert(index, Slot::Cell(cellnum));
                Some(Instruction::StoreCell(cellnum))
            }
            None => None,
        }
    }

    fn destroy(&self, compiler: &mut Compiler) -> usize {
        let mut len = 0;
        for (_, slot) in self.map.iter() {
            match slot {
                Slot::Local(i) => { compiler.instruction(Instruction::DestroyLocal(*i)); }
                Slot::Cell(i) => { compiler.instruction(Instruction::DestroyCell(*i)); }
            }
            len += 1;
        }
        len
    }
}

pub struct Compiler {
    constants: Vec<Object>,
    funcs: Vec<CompiledFunction>,
    fmt_specs: Vec<FormatSpec>,
    import_paths: Vec<String>,

    code: Vec<Instruction>,

    slots: Vec<SlotMap>,

    num_locals: usize,
    num_cells: usize,

    actions: Vec<(usize, usize, Span, Action)>,
    reasons: Vec<(usize, usize, Reason)>,
}

impl Compiler {
    pub fn compile(function: Function) -> Result<CompiledFunction, Error> {
        let Function { constants, expression, slots, fmt_specs, positional, keywords, .. } = function;
        let mut compiler = Compiler {
            constants,
            funcs: Vec::new(),
            fmt_specs,
            import_paths: Vec::new(),
            code: Vec::new(),
            slots: Vec::new(),
            num_locals: 0,
            num_cells: 0,
            actions: Vec::new(),
            reasons: Vec::new(),
        };
        compiler.push_slots(&slots);

        if let Some(args) = positional {
            compiler.emit_list_binding(&args)?;
        }
        compiler.instruction(Instruction::Discard);

        if let Some(kwargs) = keywords {
            compiler.emit_map_binding(&kwargs)?;
        }
        compiler.instruction(Instruction::Discard);

        compiler.emit_expression(&expression)?;
        compiler.pop_slots();
        Ok(compiler.finalize())
    }

    fn emit_expression(&mut self, expr: &Expr) -> Result<usize, Error> {
        match expr {
            Expr::Constant(index) => {
                self.instruction(Instruction::LoadConst(*index));
                Ok(1)
            }

            Expr::String(elements) => {
                self.instruction(Instruction::NewString);

                let mut len = 0;
                for element in elements {
                    len += self.emit_string_element(element)?;
                }
                Ok(len + 1)
            }

            Expr::Slot(loc) => {
                match self.load_instruction(*loc) {
                    Some(instruction) => {
                        self.instruction(instruction);
                        Ok(1)
                    }
                    None => { panic!("my god"); }
                }
            }

            Expr::Builtin(index) => {
                self.instruction(Instruction::LoadBuiltin(*index));
                Ok(1)
            }

            Expr::Transformed { operand, transform } => {
                let mut len = self.emit_expression(operand)?;
                len += self.emit_transform(transform)?;
                Ok(len)
            }

            Expr::Branch {
                condition,
                true_branch,
                false_branch,
            } => {
                let cond_len = self.emit_expression(condition)?;
                let cjump_index = self.instruction(Instruction::Noop);
                let false_len = self.emit_expression(false_branch)?;
                let jump_index = self.instruction(Instruction::Noop);
                let true_len = self.emit_expression(true_branch)?;

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

            Expr::Let { bindings, expression, slots } => {
                self.push_slots(slots);
                let mut len = 0;
                for (binding, expr) in bindings {
                    len += self.emit_expression(expr)?;
                    len += self.emit_binding(binding)?;
                }
                len += self.emit_expression(expression)?;
                len += self.pop_slots();
                Ok(len)
            }

            Expr::Imports { imports, expression, slots } => {
                self.push_slots(slots);
                let mut len = 0;
                for (binding, path) in imports {
                    let index = self.import_path(path.as_ref().clone());
                    let loc = self.code.len();
                    self.instruction(Instruction::Import(index));
                    self.actions.push((loc, loc + 1, path.span(), Action::Import));
                    len += self.emit_binding(binding)? + 1;
                }
                len += self.emit_expression(expression)?;
                len += self.pop_slots();
                Ok(len)
            }

            Expr::Func(function) => {
                let load_index = self.instruction(Instruction::Noop);

                let mut len = 0;
                for loc in function.requires.iter() {
                    match self.push_cell_instruction(*loc) {
                        Some(instruction) => {
                            self.instruction(instruction);
                            len += 1;
                        }
                        None => { panic!("the stars"); }
                    }
                }

                let compiled = Compiler::compile(function.clone())?;
                let index = self.function(compiled);
                self.code[load_index] = Instruction::LoadFunc(index);
                Ok(len + 1)
            }
        }
    }

    fn emit_binding(&mut self, binding: &Tagged<Binding>) -> Result<usize, Error> {
        let loc = self.code.len();

        let retval = match binding.as_ref() {
            Binding::Slot(slot) => {
                match self.store_instruction(*slot) {
                    Some(instruction) => {
                        self.instruction(instruction);
                        Ok(1)
                    }
                    None => { panic!("oh shit"); }
                }
            }

            Binding::List(binding) => {
                let len = self.emit_list_binding(binding.as_ref())?;
                self.instruction(Instruction::Discard);
                Ok(len + 1)
            }

            Binding::Map(binding) => {
                let len = self.emit_map_binding(binding)?;
                self.instruction(Instruction::Discard);
                Ok(len + 1)
            }
        };

        let end = self.code.len();
        self.actions.push((loc, end, binding.span(), Action::Bind));

        retval
    }

    fn emit_list_binding(&mut self, binding: &ListBinding) -> Result<usize, Error> {
        let mut len = 0;

        if binding.slurp.is_some() {
            self.instruction(Instruction::AssertListMinLength(
                binding.num_front + binding.num_back,
            ));
            len += 1;
        } else {
            self.instruction(Instruction::AssertListMinMaxLength(
                binding.num_front,
                binding.num_front + binding.def_front,
            ));
            len += 1;
        }

        if let Some(Some(slot)) = binding.slurp {
            self.instruction(Instruction::IntSlice {
                start: binding.num_front + binding.def_front,
                from_end: binding.num_back + binding.def_back,
            });
            match self.store_instruction(slot) {
            // match self.slots.as_mut().map(|x| x.store_instruction(slot)).flatten() {
                Some(instruction) => {
                    self.instruction(instruction);
                    len += 1;
                }
                None => { panic!("oh shit"); }
            }
            len += 2;
        }

        for (i, (sub_binding, default)) in binding.front.iter().enumerate() {
            if let Some(d) = default {
                let index = self.instruction(Instruction::Noop);
                let default_len = self.emit_expression(d.as_ref())?;
                self.code[index] = Instruction::IntIndexLAndJump {
                    index: i,
                    jump: default_len,
                };
                len += default_len + 1;
            } else {
                self.instruction(Instruction::IntIndexL(i));
                len += 1;
            }
            len += self.emit_binding(sub_binding)?;
        }

        for (i, (sub_binding, default)) in binding.back.iter().enumerate() {
            if let Some(d) = default {
                let index = self.instruction(Instruction::Noop);
                let default_len = self.emit_expression(d.as_ref())?;
                self.code[index] = Instruction::IntIndexFromEndAndJump {
                    index: i,
                    root_front: binding.num_front + binding.def_front,
                    root_back: binding.num_back + binding.def_back,
                    jump: default_len,
                };
                len += default_len + 1;
            } else {
                self.instruction(Instruction::IntIndexFromEnd {
                    index: i,
                    root_front: binding.num_front + binding.def_front,
                    root_back: binding.num_back + binding.def_back,
                });
                len += 1;
            }
            len += self.emit_binding(sub_binding)?;
        }

        Ok(len)
    }

    fn emit_map_binding(&mut self, binding: &Tagged<MapBinding>) -> Result<usize, Error> {
        let mut len = 0;

        self.instruction(Instruction::AssertMap);
        len += 1;

        for MapBindingElement { key, binding, default} in binding.elements.iter() {
            if let Some(d) = default {
                let index = self.instruction(Instruction::Noop);
                let default_len = self.emit_expression(d.as_ref())?;
                self.code[index] = Instruction::IntIndexMAndJump {
                    key: *key.as_ref(),
                    jump: default_len,
                };
                len += default_len + 1;
            } else {
                let loc = self.code.len();
                self.instruction(Instruction::IntIndexM(*key.as_ref()));
                self.actions.push((loc, loc + 1, key.span(), Action::Bind));
                self.reasons.push((loc, loc + 1, Reason::from(Unpack::KeyMissing(**key))));
            }
            len += self.emit_binding(binding)?;
        }

        if let Some(slot) = binding.slurp {
            self.instruction(Instruction::Duplicate);
            len += 1;

            for MapBindingElement { key, .. } in binding.elements.iter() {
                self.instruction(Instruction::DelKeyIfExists(*key.as_ref()));
                len += 1;
            }

            match self.store_instruction(slot) {
                Some(instruction) => {
                    self.instruction(instruction);
                    len += 1;
                }
                None => { panic!("oh shit"); }
            }

            len += 1;
        }

        Ok(len)
    }

    fn emit_string_element(&mut self, element: &StringElement) -> Result<usize, Error> {
        match element {
            StringElement::Raw(index) => {
                self.instruction(Instruction::LoadConst(*index));
                self.instruction(Instruction::Add);
                Ok(2)
            }

            StringElement::Interpolate(expr, spec) => {
                let len = self.emit_expression(expr)?;
                if let Some(index) = spec {
                    self.instruction(Instruction::FormatWithSpec(*index));
                } else {
                    self.instruction(Instruction::FormatWithDefault);
                }
                let loc = self.code.len();
                self.actions.push((loc, loc + 1, expr.span(), Action::Format));
                self.instruction(Instruction::Add);
                Ok(len + 2)
            }
        }
    }

    fn emit_list_element(&mut self, element: &ListElement) -> Result<usize, Error> {
        match element {
            ListElement::Singleton(expr) => {
                let len = self.emit_expression(expr)?;
                self.instruction(Instruction::PushToList);
                Ok(len + 1)
            }

            ListElement::Splat(expr) => {
                let len = self.emit_expression(expr)?;
                let loc = self.code.len();
                self.instruction(Instruction::SplatToCollection);
                self.actions.push((loc, loc + 1, expr.span(), Action::Splat));
                Ok(len + 1)
            }

            ListElement::Cond { condition, element } => {
                let condition_len = self.emit_expression(condition)?;
                self.instruction(Instruction::LogicalNegate);
                let index = self.instruction(Instruction::Noop);
                let element_len = self.emit_list_element(element)?;
                self.code[index] = Instruction::CondJump(element_len);
                Ok(condition_len + element_len + 2)
            }

            ListElement::Loop { binding, iterable, element, slots } => {
                let iterable_len = self.emit_expression(iterable)?;
                let loc = self.code.len();
                self.instruction(Instruction::NewIterator);
                self.actions.push((loc, loc + 1, iterable.span(), Action::Iterate));

                self.push_slots(slots);

                let index = self.instruction(Instruction::Noop);
                let mut jump_len = self.emit_binding(binding)?;
                self.instruction(Instruction::Interchange);
                jump_len += self.emit_list_element(element)?;
                self.instruction(Instruction::Interchange);
                self.instruction(Instruction::JumpBack(jump_len + 4));
                self.code[index] = Instruction::NextOrJump(jump_len + 3);
                self.instruction(Instruction::Discard);

                let pop_len = self.pop_slots();
                Ok(iterable_len + jump_len + pop_len + 6)
            }
        }
    }

    fn emit_map_element(&mut self, element: &MapElement) -> Result<usize, Error> {
        match element {
            MapElement::Singleton { key, value } => {
                let loc = self.code.len();
                let mut len = self.emit_expression(key)?;
                self.actions.push((loc, self.code.len(), key.span(), Action::Assign));
                len += self.emit_expression(value)?;
                self.instruction(Instruction::PushToMap);
                Ok(len + 1)
            }

            MapElement::Splat(expr) => {
                let len = self.emit_expression(expr)?;
                let loc = self.code.len();
                self.instruction(Instruction::SplatToCollection);
                self.actions.push((loc, loc + 1, expr.span(), Action::Splat));
                Ok(len + 1)
            }

            MapElement::Cond { condition, element } => {
                let condition_len = self.emit_expression(condition)?;
                self.instruction(Instruction::LogicalNegate);
                let index = self.instruction(Instruction::Noop);
                let element_len = self.emit_map_element(element)?;
                self.code[index] = Instruction::CondJump(element_len);
                Ok(condition_len + element_len + 2)
            }

            MapElement::Loop { binding, iterable, element, slots } => {
                let iterable_len = self.emit_expression(iterable)?;
                let loc = self.code.len();
                self.instruction(Instruction::NewIterator);
                self.actions.push((loc, loc + 1, iterable.span(), Action::Iterate));

                self.push_slots(slots);

                let index = self.instruction(Instruction::Noop);
                let mut jump_len = self.emit_binding(binding)?;
                self.instruction(Instruction::Interchange);
                jump_len += self.emit_map_element(element)?;
                self.instruction(Instruction::Interchange);
                self.instruction(Instruction::JumpBack(jump_len + 4));
                self.code[index] = Instruction::NextOrJump(jump_len + 3);
                self.instruction(Instruction::Discard);

                let pop_len = self.pop_slots();
                Ok(iterable_len + jump_len + pop_len + 6)
            }
        }
    }

    fn emit_transform(&mut self, transform: &Transform) -> Result<usize, Error> {
        match transform {
            Transform::UnOp(op) => {
                let loc = self.code.len();
                let len = match op.as_ref() {
                    UnOp::Passthrough => 0,
                    UnOp::ArithmeticalNegate => {
                        self.code.push(Instruction::ArithmeticalNegate);
                        1
                    }
                    UnOp::LogicalNegate => {
                        self.code.push(Instruction::LogicalNegate);
                        1
                    }
                };

                if len > 0 {
                    self.actions
                        .push((loc, loc + len, op.span(), Action::Evaluate));
                }
                Ok(len)
            }

            Transform::BinOp(operator, operand) => {
                match operator.as_ref() {
                    BinOp::Or => {
                        self.instruction(Instruction::Duplicate);
                        let cjump_index = self.instruction(Instruction::Noop);
                        self.instruction(Instruction::Discard);
                        let false_len = self.emit_expression(operand)?;
                        self.code[cjump_index] = Instruction::CondJump(false_len + 1);
                        return Ok(false_len + 3);
                    }
                    BinOp::And => {
                        self.instruction(Instruction::Duplicate);
                        self.instruction(Instruction::CondJump(1));
                        let jump_index = self.instruction(Instruction::Noop);
                        self.instruction(Instruction::Discard);
                        let true_len = self.emit_expression(operand)?;
                        self.code[jump_index] = Instruction::Jump(true_len + 1);
                        return Ok(true_len + 4);
                    }
                    _ => {}
                }

                let len = self.emit_expression(operand.as_ref())?;
                let loc = self.code.len();

                match operator.as_ref() {
                    BinOp::Power => {
                        self.code.push(Instruction::Power);
                    }
                    BinOp::Multiply => {
                        self.code.push(Instruction::Multiply);
                    }
                    BinOp::IntegerDivide => {
                        self.code.push(Instruction::IntegerDivide);
                    }
                    BinOp::Divide => {
                        self.code.push(Instruction::Divide);
                    }
                    BinOp::Add => {
                        self.code.push(Instruction::Add);
                    }
                    BinOp::Subtract => {
                        self.code.push(Instruction::Subtract);
                    }
                    BinOp::Less => {
                        self.code.push(Instruction::Less);
                    }
                    BinOp::Greater => {
                        self.code.push(Instruction::Greater);
                    }
                    BinOp::LessEqual => {
                        self.code.push(Instruction::LessEqual);
                    }
                    BinOp::GreaterEqual => {
                        self.code.push(Instruction::GreaterEqual);
                    }
                    BinOp::Equal => {
                        self.code.push(Instruction::Equal);
                    }
                    BinOp::NotEqual => {
                        self.code.push(Instruction::NotEqual);
                    }
                    BinOp::Contains => {
                        self.code.push(Instruction::Contains);
                    }
                    BinOp::Index => {
                        self.code.push(Instruction::Index);
                    }
                    BinOp::Or | BinOp::And => {}
                };

                self.actions
                    .push((loc, loc + 1, operator.span(), Action::Evaluate));
                Ok(len + 1)
            }

            Transform::FunCall(args, add_action) => {
                self.instruction(Instruction::NewMap);
                self.instruction(Instruction::NewList);

                let mut len = 0;
                for arg in args.iter() {
                    len += self.emit_arg_element(arg)?;
                }

                let loc = self.code.len();
                self.instruction(Instruction::Call);
                if *add_action {
                    self.actions.push((loc, loc + 1, args.span(), Action::Evaluate));
                }

                Ok(len + 3)
            }
        }
    }

    fn emit_arg_element(&mut self, arg: &ArgElement) -> Result<usize, Error> {
        match arg {
            ArgElement::Singleton(expr) => {
                let len = self.emit_expression(expr)?;
                self.instruction(Instruction::PushToList);
                Ok(len + 1)
            }

            ArgElement::Keyword(key, expr) => {
                let len = self.emit_expression(expr)?;
                self.instruction(Instruction::IntPushToKwargs(**key));
                Ok(len + 1)
            }

            ArgElement::Splat(expr) => {
                let len = self.emit_expression(expr)?;
                let loc = self.code.len();
                self.instruction(Instruction::IntArgSplat);
                self.actions
                    .push((loc, loc + 1, expr.span(), Action::Splat));
                Ok(len + 1)
            }
        }
    }

    fn instruction(&mut self, instruction: Instruction) -> usize {
        let r = self.code.len();
        self.code.push(instruction);

        match instruction {
            Instruction::StoreLocal(i) => {
                self.num_locals = self.num_locals.max(i + 1);
            }
            Instruction::LoadLocal(i) => {
                self.num_locals = self.num_locals.max(i + 1);
            }
            Instruction::StoreCell(i) => {
                self.num_cells = self.num_cells.max(i + 1);
            }
            Instruction::LoadCell(i) => {
                self.num_cells = self.num_cells.max(i + 1);
            }
            _ => {}
        }

        r
    }

    fn push_cell_instruction(&mut self, loc: BindingLoc) -> Option<Instruction> {
        match loc {
            BindingLoc::Enclosed(i) => Some(Instruction::PushEnclosedToClosure(i)),
            _ => match self.load_instruction(loc) {
                Some(Instruction::LoadCell(i)) => Some(Instruction::PushCellToClosure(i)),
                _ => None,
            }
        }
    }

    fn load_instruction(&mut self, loc: BindingLoc) -> Option<Instruction> {
        match loc {
            BindingLoc::Enclosed(i) => { Some(Instruction::LoadEnclosed(i)) }
            BindingLoc::Slot(index) => {
                for map in self.slots.iter_mut().rev() {
                    let result = map.load_instruction(index);
                    if result.is_some() {
                        return result;
                    }
                }
                None
            }
        }
    }

    fn store_instruction(&mut self, index: usize) -> Option<Instruction> {
        for map in self.slots.iter_mut().rev() {
            let result = map.store_instruction(index);
            if result.is_some() {
                return result;
            }
        }
        None
    }

    fn push_slots(&mut self, slots: &SlotCatalog) {
        let new = SlotMap::new(self.slots.last(), slots.clone());
        self.slots.push(new);
    }

    fn pop_slots(&mut self) -> usize {
        let catalog = self.slots.pop().unwrap();
        catalog.destroy(self)
    }

    fn function(&mut self, function: CompiledFunction) -> usize {
        let r = self.funcs.len();
        self.funcs.push(function);
        r
    }

    fn import_path(&mut self, path: String) -> usize {
        let r = self.import_paths.len();
        self.import_paths.push(path);
        r
    }

    fn build_trace(&mut self) -> IntervalTree<usize, (Span, Action), Reason> {
        let mut endpoints: HashSet<usize> = HashSet::new();
        for (left, right, ..) in &self.actions {
            endpoints.insert(*left);
            endpoints.insert(*right);
        }
        for (left, right, ..) in &self.reasons {
            endpoints.insert(*left);
            endpoints.insert(*right);
        }

        let mut endpoints: Vec<usize> = endpoints.iter().copied().collect();
        endpoints.sort();

        let mut tree: IntervalTree<usize, (Span, Action), Reason> = IntervalTree::new(endpoints);

        while !self.actions.is_empty() {
            let (left, right, span, action) = self.actions.pop().unwrap();
            tree.insert_first(left, right, (span, action));
        }

        while !self.reasons.is_empty() {
            let (left, right, reason) = self.reasons.pop().unwrap();
            tree.insert_second(left, right, reason);
        }

        tree
    }

    fn finalize(mut self) -> CompiledFunction {
        self.code.push(Instruction::Return);

        let trace = self.build_trace();

        CompiledFunction {
            functions: self.funcs,
            constants: self.constants,
            code: self.code,
            fmt_specs: self.fmt_specs,
            import_paths: self.import_paths,
            num_locals: self.num_locals,
            num_cells: self.num_cells,
            trace,
        }
    }
}
