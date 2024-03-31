use std::collections::{HashMap, HashSet};

use gc::{Finalize, Trace};
use serde::{Deserialize, Serialize};

use crate::ast::low::{
    ArgElement, Binding, Expr, Function, ListBinding, ListElement, MapBinding, MapBindingElement,
    MapElement, StringElement, Transform,
};
use crate::ast::{BindingLoc, SlotCatalog, SlotType};
use crate::error::{Action, IntervalTree, Reason, Span, Tagged, Unpack};
use crate::formatting::FormatSpec;
use crate::types::{BinOp, Key, LogicOp, Res};
use crate::Object;

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
    // ------------------------------------------------------------------------------------------------
    /// Load the given object from the constants array and push it on the stack.
    LoadConst(usize),

    /// Load the given object from the locals array and push it on the stack.
    LoadLocal(usize),

    /// Load the given object from the cell array and push it on the stack.
    LoadCell(usize),

    /// Load the given object from the enclosed array and push it on the stack.
    LoadEnclosed(usize),

    /// Load the given function object, wrap it into a closure and push it on the stack.
    LoadFunc(usize),

    /// Load the given builtin from the global BUILTINS array and push it on the stack.
    LoadBuiltin(usize),

    /// Process the given import path and push the result on the stack.
    Import(usize),

    // Storing
    // ------------------------------------------------------------------------------------------------
    /// Pop the stack and push the object to the local array at the given index.
    StoreLocal(usize),

    /// Pop the stack and push the object to the cell array at the given index.
    StoreCell(usize),

    // Destroying
    // ------------------------------------------------------------------------------------------------
    /// Reset the slot in the local array at the given index.
    DestroyLocal(usize),

    /// Reset the slot in the cell array at the given index.
    /// This should not mutate the existing cell, just replace it with a new one.
    DestroyCell(usize),

    // Control flow
    // ------------------------------------------------------------------------------------------------
    /// Pop the stack and push the object to the lower frame's stack.
    Return,

    /// Pop the stack, and jump the given number of instructions if the object is truthy.
    CondJump(usize),

    /// Jump the given number of instructions unconditionally. Not that, since
    /// the VM advances over this instruction before executing it, the delta
    /// must NOT count this instruction.
    Jump(usize),

    /// Jump the given number of instructions in reverse, unconditionally. Note
    /// that, since the VM advances over this instruction before executing it,
    /// the delta must count this instruction as well.
    JumpBack(usize),

    /// Clone the object on the top of the stack and push it.
    Duplicate,

    /// Drop the object on the top of the stack.
    Discard,

    /// Drop several objects on the top of the stack.
    DiscardMany(usize),

    /// Interchange the top two objects on the stack.
    Interchange,

    /// Call the function at `stack[2]` using `stack[0]` as arguments (must be a
    /// list) and `stack[1]` as keyword arguments (must be a map).
    Call,

    /// Do nothing.
    Noop,

    // Asserts
    // ------------------------------------------------------------------------------------------------
    /// Throw an error unless the top of the stack is a list with at least the
    /// given length.
    AssertListMinLength(usize),

    /// Throw an error unless the top of the stack is a list with at least the
    /// given minimum length and at most the given maximum length.
    AssertListMinMaxLength(usize, usize),

    /// Throw an error unless the top of the stack is a map.
    AssertMap,

    // Unary operators
    // ------------------------------------------------------------------------------------------------
    /// Apply the unary mathematical negation operator to the top of the stack and push the result.
    ArithmeticalNegate,

    /// Apply the unary logical negation operator to the top of the stack and push the result.
    LogicalNegate,

    /// Format the top of the stack with the given format specification and push the result.
    FormatWithSpec(usize),

    /// Format the top of the stack with the default format specification and push the result.
    FormatWithDefault,

    // Binary mathematical operators
    // ------------------------------------------------------------------------------------------------
    /// Pop y and x from the stack, then push `x + y`.
    Add,

    /// Pop y and x from the stack, then push `x - y`.
    Subtract,

    /// Pop y and x from the stack, then push `x * y`.
    Multiply,

    /// Pop y and x from the stack, then push `x // y`.
    IntegerDivide,

    /// Pop y and x from the stack, then push `x / y`.
    Divide,

    /// Pop y and x from the stack, then push `x ^ y`.
    Power,

    // Binary comparison operators
    // ------------------------------------------------------------------------------------------------
    /// Pop y and x from the stack, then push `x < y`.
    Less,

    /// Pop y and x from the stack, then push `x > y`.
    Greater,

    /// Pop y and x from the stack, then push `x <= y`.
    LessEqual,

    /// Pop y and x from the stack, then push `x >= y`.
    GreaterEqual,

    /// Pop y and x from the stack, then push `x == y`.
    Equal,

    /// Pop y and x from the stack, then push `x != y`.
    NotEqual,

    /// Pop y and x from the stack, then push `x has y`.
    Contains,

    // Other operators
    // ------------------------------------------------------------------------------------------------
    /// Pop y and x from the stack, then push `x[y]`.
    Index,

    // Constructors
    // ------------------------------------------------------------------------------------------------
    /// Push a new empty list on the stack.
    NewList,

    /// Push a new empty map on the stack.
    NewMap,

    /// Pop the stack and convert the object into an iterator, then push it on the stack.
    NewIterator,

    /// Push a new empty string on the stack.
    NewString,

    // Mutability
    // ------------------------------------------------------------------------------------------------
    /// Pop the stack and push the object to the list on the top of the stack.
    PushToList,

    /// Pop the top two stack objects (value and key) and push them to the map
    /// on the top of the stack.
    PushToMap,

    /// Pop the stack and insert all its elements into the object on the top of
    /// the stack.
    SplatToCollection,

    /// Remove the key from the map at the top of the stack, if it exists.
    DelKeyIfExists(Key),

    /// Load the cell at the given index and push it to the closure at the top
    /// of the stack. Important: the cell must be pushed as-is. It should not be
    /// unwrapped.
    PushCellToClosure(usize),

    /// Load the cell at the given enclosure index and push it to the closure at
    /// the top of the stack. Important: the cell must be pushed as-is. It
    /// should not be unwrapped.
    PushEnclosedToClosure(usize),

    /// Get the next element from the iterator at the top of the stack and push
    /// it on the stack. If there are no more elements, jump the given delta.
    NextOrJump(usize),

    // Shortcuts for internal use
    // ------------------------------------------------------------------------------------------------
    /// Get the element from the list at the top of the stack at the given
    /// index, and push it on the stack.
    IntIndexL(usize),

    /// Get the element from the list at the top of the stack at the given
    /// index, push it on the stack and then jump the given delta. Do not error
    /// or jump if the index does not exist.
    IntIndexLAndJump { index: usize, jump: usize },

    /// Get the element from the list at the top of the stack at the given index
    /// counted from the end, and push it on the stack.
    IntIndexFromEnd {
        index: usize,
        root_front: usize,
        root_back: usize,
    },

    /// Get the element from the list at the top of the stack at the giv index
    /// counted from the end, push it on the stack and then jump the given
    /// delta. Do not error or jump if the index does not exist.
    IntIndexFromEndAndJump {
        index: usize,
        root_front: usize,
        root_back: usize,
        jump: usize,
    },

    /// Extract the given slice from the list at the top of the stack and push
    /// it to the stack.
    IntSlice { start: usize, from_end: usize },

    /// Get the element from the map at the top of the stack and push it on the
    /// stack.
    IntIndexM(Key),

    /// Get the element from the map at the top of the stack, push it on the
    /// stack and then jump the given delta. Do not error or jump if the key
    /// does not exist.
    IntIndexMAndJump { key: Key, jump: usize },

    /// Pop the stack and push the object to the kwargs map (located at
    /// `stack[1]`) with the given key.
    IntPushToKwargs(Key),

    /// Pop the stack and insert the elements into either the args list (located
    /// at `stack[0]`) or the kwargs map (located at `stack[1]`), depending on
    /// whether it's a list or a map.
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
            Some(Slot::Local(i)) => {
                return Some(Instruction::LoadLocal(*i));
            }
            Some(Slot::Cell(i)) => {
                return Some(Instruction::LoadCell(*i));
            }
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
            Some(Slot::Local(i)) => {
                return Some(Instruction::StoreLocal(*i));
            }
            Some(Slot::Cell(i)) => {
                return Some(Instruction::StoreCell(*i));
            }
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
                Slot::Local(i) => {
                    compiler.instruction(Instruction::DestroyLocal(*i));
                }
                Slot::Cell(i) => {
                    compiler.instruction(Instruction::DestroyCell(*i));
                }
            }
            len += 1;
        }
        len
    }
}

trait WrapCompiler: Sized {
    fn compiler(&mut self) -> &mut Compiler;

    fn instruction(mut self, instruction: Instruction) -> Self {
        self.compiler().instruction(instruction);
        self
    }

    fn emit_expression(mut self, expr: Expr) -> Res<Self> {
        self.compiler().emit_expression(expr)?;
        Ok(self)
    }

    fn emit_binding(mut self, binding: Tagged<Binding>) -> Res<Self> {
        self.compiler().emit_binding(binding)?;
        Ok(self)
    }

    fn emit_list_binding(mut self, binding: ListBinding) -> Res<Self> {
        self.compiler().emit_list_binding(binding)?;
        Ok(self)
    }

    fn emit_map_binding(mut self, binding: MapBinding) -> Res<Self> {
        self.compiler().emit_map_binding(binding)?;
        Ok(self)
    }

    fn emit_list_element(mut self, element: ListElement) -> Res<Self> {
        self.compiler().emit_list_element(element)?;
        Ok(self)
    }

    fn emit_map_element(mut self, element: MapElement) -> Res<Self> {
        self.compiler().emit_map_element(element)?;
        Ok(self)
    }

    fn store_instruction(mut self, index: usize) -> Option<Self> {
        self.compiler().store_instruction(index)?;
        Some(self)
    }
}

struct TraceWrapper<'a> {
    compiler: &'a mut Compiler,
    span: Span,
    action: Action,
    reason: Option<Reason>,

    start: usize,
}

impl<'a> WrapCompiler for TraceWrapper<'a> {
    fn compiler(&mut self) -> &mut Compiler {
        self.compiler
    }
}

impl<'a> TraceWrapper<'a> {
    fn new(compiler: &'a mut Compiler, span: Span, action: Action) -> Self {
        let start = compiler.code.len();
        Self {
            compiler,
            span,
            action,
            start,
            reason: None,
        }
    }

    fn reason<T>(mut self, reason: T) -> Self
    where
        Reason: From<T>,
    {
        self.reason = Some(Reason::from(reason));
        self
    }

    fn finalize(self) -> usize {
        self.compiler
            .actions
            .push((self.start, self.compiler.code.len(), self.span, self.action));
        if let Some(reason) = self.reason {
            self.compiler
                .reasons
                .push((self.start, self.compiler.code.len(), reason));
        }
        self.compiler.code.len() - self.start
    }
}

struct JumpWrapper<'a> {
    compiler: &'a mut Compiler,
    start: usize,
}

impl<'a> WrapCompiler for JumpWrapper<'a> {
    fn compiler(&mut self) -> &mut Compiler {
        self.compiler
    }
}

impl<'a> JumpWrapper<'a> {
    fn new(compiler: &'a mut Compiler) -> Self {
        let start = compiler.code.len();
        compiler.code.push(Instruction::Noop);
        Self { compiler, start }
    }

    fn to_start<F: Fn(usize) -> Instruction>(mut self, to_start: F) -> Self {
        let len = self.compiler().code.len() + 1 - self.start;
        self.compiler.instruction(to_start(len));
        self
    }

    fn finalize<F: Fn(usize) -> Instruction>(self, finalizer: F) -> usize {
        let len = self.compiler.code.len() - self.start;
        self.compiler.code[self.start] = finalizer(len - 1);
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
    pub fn compile(function: Function) -> Res<CompiledFunction> {
        let Function {
            constants,
            expression,
            slots,
            fmt_specs,
            positional,
            keywords,
            ..
        } = function;
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
        compiler.push_slots(slots);

        if let Some(args) = positional {
            compiler.emit_list_binding(args.unwrap())?;
        }
        compiler.instruction(Instruction::Discard);

        if let Some(kwargs) = keywords {
            compiler.emit_map_binding(kwargs.unwrap())?;
        }
        compiler.instruction(Instruction::Discard);

        compiler.emit_expression(expression.unwrap())?;
        compiler.pop_slots();
        Ok(compiler.finalize())
    }

    fn emit_expression(&mut self, expr: Expr) -> Res<usize> {
        match expr {
            Expr::Constant(index) => Ok(self.instruction(Instruction::LoadConst(index))),
            Expr::Slot(loc) => Ok(self.load_instruction(loc).unwrap()),
            Expr::Builtin(index) => Ok(self.instruction(Instruction::LoadBuiltin(index))),

            Expr::String(elements) => {
                let mut len = self.instruction(Instruction::NewString);
                for element in elements {
                    len += self.emit_string_element(element)?;
                }
                Ok(len + 1)
            }

            Expr::Transformed { operand, transform } => {
                let mut len = self.emit_expression(operand.unwrap())?;
                len += self.emit_transform(transform)?;
                Ok(len)
            }

            Expr::Branch {
                condition,
                true_branch,
                false_branch,
            } => {
                let mut len = self.emit_expression(condition.unwrap())?;
                len += self
                    .with_jump()
                    .emit_expression(false_branch.unwrap())?
                    .finalize(|l| Instruction::CondJump(l + 1));
                len += self
                    .with_jump()
                    .emit_expression(true_branch.unwrap())?
                    .finalize(|l| Instruction::Jump(l));
                Ok(len)
            }

            Expr::List(elements) => {
                let mut len = self.instruction(Instruction::NewList);
                for element in elements {
                    len += self.emit_list_element(element.unwrap())?;
                }
                Ok(len)
            }

            Expr::Map(elements) => {
                let mut len = self.instruction(Instruction::NewMap);
                for element in elements {
                    len += self.emit_map_element(element.unwrap())?;
                }
                Ok(len)
            }

            Expr::Let {
                bindings,
                expression,
                slots,
            } => {
                self.push_slots(slots);
                let mut len = 0;
                for (binding, expr) in bindings {
                    len += self.emit_expression(expr.unwrap())?;
                    len += self.emit_binding(binding)?;
                }
                len += self.emit_expression(expression.unwrap())?;
                len += self.pop_slots();
                Ok(len)
            }

            Expr::Imports {
                imports,
                expression,
                slots,
            } => {
                self.push_slots(slots);
                let mut len = 0;
                for (binding, path) in imports {
                    let index = self.import_path(path.as_ref().clone());
                    len += self
                        .with_trace(path.span(), Action::Import)
                        .instruction(Instruction::Import(index))
                        .finalize();
                    len += self.emit_binding(binding)?;
                }
                len += self.emit_expression(expression.unwrap())?;
                len += self.pop_slots();
                Ok(len)
            }

            Expr::Func(mut function) => {
                let requires = function.requires.take();

                let compiled = Compiler::compile(function)?;
                let index = self.function(compiled);
                let mut len = self.instruction(Instruction::LoadFunc(index));

                if let Some(requires) = requires {
                    for loc in requires {
                        len += self.push_cell_instruction(loc).unwrap();
                    }
                }

                Ok(len)
            }
        }
    }

    fn emit_binding(&mut self, binding: Tagged<Binding>) -> Res<usize> {
        let (binding, span) = binding.decompose();
        match binding {
            Binding::Slot(slot) => Ok(self
                .with_trace(span, Action::Bind)
                .store_instruction(slot)
                .unwrap()
                .finalize()),
            Binding::List(binding) => Ok(self
                .with_trace(span, Action::Bind)
                .emit_list_binding(binding.unwrap())?
                .instruction(Instruction::Discard)
                .finalize()),
            Binding::Map(binding) => Ok(self
                .with_trace(span, Action::Bind)
                .emit_map_binding(binding.unwrap())?
                .instruction(Instruction::Discard)
                .finalize()),
        }
    }

    fn emit_list_binding(&mut self, binding: ListBinding) -> Res<usize> {
        let mut len = 0;

        if binding.slurp.is_some() {
            len += self.instruction(Instruction::AssertListMinLength(
                binding.num_front + binding.num_back,
            ));
        } else {
            len += self.instruction(Instruction::AssertListMinMaxLength(
                binding.num_front,
                binding.num_front + binding.def_front,
            ));
        }

        if let Some(Some(slot)) = binding.slurp {
            len += self.instruction(Instruction::IntSlice {
                start: binding.num_front + binding.def_front,
                from_end: binding.num_back + binding.def_back,
            });
            len += self.store_instruction(slot).unwrap();
        }

        for (i, (sub_binding, default)) in binding.front.into_iter().enumerate() {
            if let Some(d) = default {
                len += self
                    .with_jump()
                    .emit_expression(d.unwrap())?
                    .finalize(|l| Instruction::IntIndexLAndJump { index: i, jump: l });
            } else {
                len += self.instruction(Instruction::IntIndexL(i));
            }
            len += self.emit_binding(sub_binding)?;
        }

        for (i, (sub_binding, default)) in binding.back.into_iter().enumerate() {
            if let Some(d) = default {
                len += self.with_jump().emit_expression(d.unwrap())?.finalize(|l| {
                    Instruction::IntIndexFromEndAndJump {
                        index: i,
                        root_front: binding.num_front + binding.def_front,
                        root_back: binding.num_back + binding.def_back,
                        jump: l,
                    }
                });
            } else {
                len += self.instruction(Instruction::IntIndexFromEnd {
                    index: i,
                    root_front: binding.num_front + binding.def_front,
                    root_back: binding.num_back + binding.def_back,
                });
            }
            len += self.emit_binding(sub_binding)?;
        }

        Ok(len)
    }

    fn emit_map_binding(&mut self, binding: MapBinding) -> Res<usize> {
        let mut len = self.instruction(Instruction::AssertMap);

        if let Some(slot) = binding.slurp {
            len += self.instruction(Instruction::Duplicate);
            for MapBindingElement { key, .. } in binding.elements.iter() {
                len += self.instruction(Instruction::DelKeyIfExists(*key.as_ref()));
            }
            len += self.store_instruction(slot).unwrap();
        }

        for MapBindingElement {
            key,
            binding,
            default,
        } in binding.elements.into_iter()
        {
            if let Some(d) = default {
                len += self.with_jump().emit_expression(d.unwrap())?.finalize(|l| {
                    Instruction::IntIndexMAndJump {
                        key: key.unwrap(),
                        jump: l,
                    }
                });
            } else {
                let (key, span) = key.decompose();
                len += self
                    .with_trace(span, Action::Bind)
                    .reason(Unpack::KeyMissing(key))
                    .instruction(Instruction::IntIndexM(key))
                    .finalize();
            }
            len += self.emit_binding(binding)?;
        }

        Ok(len)
    }

    fn emit_string_element(&mut self, element: StringElement) -> Res<usize> {
        match element {
            StringElement::Raw(index) => {
                let mut len = self.instruction(Instruction::LoadConst(index));
                len += self.instruction(Instruction::Add);
                Ok(len)
            }

            StringElement::Interpolate(expr, spec) => {
                let (expr, span) = expr.decompose();
                let mut len = self.emit_expression(expr)?;
                if let Some(index) = spec {
                    len += self.instruction(Instruction::FormatWithSpec(index));
                } else {
                    len += self.instruction(Instruction::FormatWithDefault);
                }
                len += self
                    .with_trace(span, Action::Format)
                    .instruction(Instruction::Add)
                    .finalize();
                Ok(len)
            }
        }
    }

    fn emit_list_element(&mut self, element: ListElement) -> Res<usize> {
        match element {
            ListElement::Singleton(expr) => {
                let mut len = self.emit_expression(expr.unwrap())?;
                len += self.instruction(Instruction::PushToList);
                Ok(len)
            }

            ListElement::Splat(expr) => {
                let (expr, span) = expr.decompose();
                let mut len = self.emit_expression(expr)?;
                len += self
                    .with_trace(span, Action::Splat)
                    .instruction(Instruction::SplatToCollection)
                    .finalize();
                Ok(len)
            }

            ListElement::Cond { condition, element } => {
                let mut len = self.emit_expression(condition.unwrap())?;
                len += self.instruction(Instruction::LogicalNegate);
                len += self
                    .with_jump()
                    .emit_list_element(element.unwrap())?
                    .finalize(Instruction::CondJump);
                Ok(len)
            }

            ListElement::Loop {
                binding,
                iterable,
                element,
                slots,
            } => {
                let (iterable, span) = iterable.decompose();
                let mut len = self.emit_expression(iterable)?;

                len += self
                    .with_trace(span, Action::Iterate)
                    .instruction(Instruction::NewIterator)
                    .finalize();

                self.push_slots(slots);

                len += self
                    .with_jump()
                    .emit_binding(binding)?
                    .instruction(Instruction::Interchange)
                    .emit_list_element(element.unwrap())?
                    .instruction(Instruction::Interchange)
                    .to_start(Instruction::JumpBack)
                    .finalize(Instruction::NextOrJump);

                len += self.instruction(Instruction::Discard);
                len += self.pop_slots();
                Ok(len)
            }
        }
    }

    fn emit_map_element(&mut self, element: MapElement) -> Res<usize> {
        match element {
            MapElement::Singleton { key, value } => {
                let (key, span) = key.decompose();
                let mut len = self
                    .with_trace(span, Action::Assign)
                    .emit_expression(key)?
                    .finalize();
                len += self.emit_expression(value.unwrap())?;
                len += self.instruction(Instruction::PushToMap);
                Ok(len)
            }

            MapElement::Splat(expr) => {
                let (expr, span) = expr.decompose();
                let mut len = self.emit_expression(expr)?;
                len += self
                    .with_trace(span, Action::Splat)
                    .instruction(Instruction::SplatToCollection)
                    .finalize();
                Ok(len)
            }

            MapElement::Cond { condition, element } => {
                let mut len = self.emit_expression(condition.unwrap())?;
                len += self.instruction(Instruction::LogicalNegate);
                len += self
                    .with_jump()
                    .emit_map_element(element.unwrap())?
                    .finalize(Instruction::CondJump);
                Ok(len)
            }

            MapElement::Loop {
                binding,
                iterable,
                element,
                slots,
            } => {
                let (iterable, span) = iterable.decompose();
                let mut len = self.emit_expression(iterable)?;

                len += self
                    .with_trace(span, Action::Iterate)
                    .instruction(Instruction::NewIterator)
                    .finalize();

                self.push_slots(slots);

                len += self
                    .with_jump()
                    .emit_binding(binding)?
                    .instruction(Instruction::Interchange)
                    .emit_map_element(element.unwrap())?
                    .instruction(Instruction::Interchange)
                    .to_start(Instruction::JumpBack)
                    .finalize(Instruction::NextOrJump);

                len += self.instruction(Instruction::Discard);
                len += self.pop_slots();
                Ok(len)
            }
        }
    }

    fn emit_transform(&mut self, transform: Transform) -> Res<usize> {
        match transform {
            Transform::UnOp(op) => {
                let (op, span) = op.decompose();
                if let Some(op) = op {
                    let len = self
                        .with_trace(span, Action::Evaluate)
                        .instruction(op.instruction())
                        .finalize();
                    Ok(len)
                } else {
                    Ok(0)
                }
            }

            Transform::BinOp(operator, operand) => {
                let (operator, span) = operator.decompose();
                match operator {
                    BinOp::Logic(LogicOp::Or) => {
                        let mut len = self.instruction(Instruction::Duplicate);
                        len += self
                            .with_jump()
                            .instruction(Instruction::Discard)
                            .emit_expression(operand.unwrap())?
                            .finalize(Instruction::CondJump);
                        Ok(len)
                    }
                    BinOp::Logic(LogicOp::And) => {
                        let mut len = self.instruction(Instruction::Duplicate);
                        len += self.instruction(Instruction::CondJump(1));
                        len += self
                            .with_jump()
                            .instruction(Instruction::Discard)
                            .emit_expression(operand.unwrap())?
                            .finalize(Instruction::Jump);
                        Ok(len)
                    }
                    BinOp::Eager(op) => {
                        let mut len = self.emit_expression(operand.unwrap())?;
                        len += self
                            .with_trace(span, Action::Evaluate)
                            .instruction(op.instruction())
                            .finalize();
                        Ok(len)
                    }
                }
            }

            Transform::FunCall(args, add_action) => {
                let mut len = self.instruction(Instruction::NewMap);
                len += self.instruction(Instruction::NewList);

                let (args, span) = args.decompose();
                for arg in args.into_iter() {
                    len += self.emit_arg_element(arg.unwrap())?;
                }

                if add_action {
                    len += self
                        .with_trace(span, Action::Evaluate)
                        .instruction(Instruction::Call)
                        .finalize();
                } else {
                    len += self.instruction(Instruction::Call);
                }

                Ok(len)
            }
        }
    }

    fn emit_arg_element(&mut self, arg: ArgElement) -> Res<usize> {
        match arg {
            ArgElement::Singleton(expr) => {
                let mut len = self.emit_expression(expr.unwrap())?;
                len += self.instruction(Instruction::PushToList);
                Ok(len)
            }

            ArgElement::Keyword(key, expr) => {
                let mut len = self.emit_expression(expr.unwrap())?;
                len += self.instruction(Instruction::IntPushToKwargs(*key));
                Ok(len)
            }

            ArgElement::Splat(expr) => {
                let (expr, span) = expr.decompose();
                let mut len = self.emit_expression(expr)?;
                len += self
                    .with_trace(span, Action::Splat)
                    .instruction(Instruction::IntArgSplat)
                    .finalize();
                Ok(len)
            }
        }
    }

    fn instruction(&mut self, instruction: Instruction) -> usize {
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

        1
    }

    fn push_cell_instruction(&mut self, loc: BindingLoc) -> Option<usize> {
        match loc {
            BindingLoc::Enclosed(i) => {
                Some(self.instruction(Instruction::PushEnclosedToClosure(i)))
            }
            _ => match self.load_instruction_impl(loc) {
                Some(Instruction::LoadCell(i)) => {
                    Some(self.instruction(Instruction::PushCellToClosure(i)))
                }
                _ => None,
            },
        }
    }

    fn load_instruction_impl(&mut self, loc: BindingLoc) -> Option<Instruction> {
        match loc {
            BindingLoc::Enclosed(i) => Some(Instruction::LoadEnclosed(i)),
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

    fn load_instruction(&mut self, loc: BindingLoc) -> Option<usize> {
        match self.load_instruction_impl(loc) {
            Some(instruction) => Some(self.instruction(instruction)),
            None => None,
        }
    }

    fn store_instruction(&mut self, index: usize) -> Option<usize> {
        for map in self.slots.iter_mut().rev() {
            let result = map.store_instruction(index);
            if let Some(instruction) = result {
                return Some(self.instruction(instruction));
            }
        }
        None
    }

    fn push_slots(&mut self, slots: SlotCatalog) {
        let new = SlotMap::new(self.slots.last(), slots);
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

    fn with_trace<'a>(&'a mut self, span: Span, action: Action) -> TraceWrapper<'a> {
        TraceWrapper::new(self, span, action)
    }

    fn with_jump<'a>(&'a mut self) -> JumpWrapper<'a> {
        JumpWrapper::new(self)
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
