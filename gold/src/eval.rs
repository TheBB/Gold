use std::cmp::Ordering;
use std::path::PathBuf;
use std::rc::Rc;

#[cfg(feature = "python")]
use pyo3::{Py, FromPyObject, PyAny, PyResult, Python, pyclass, pymethods};

#[cfg(feature = "python")]
use pyo3::exceptions::PyTypeError;

#[cfg(feature = "python")]
use pyo3::types::{PyString, PyTuple};

use crate::builtins::BUILTINS;
use crate::compile::{CompiledFunction, Instruction};
use crate::error::{BindingType, Error, Internal, Reason, TypeMismatch, Unpack};
use crate::formatting::FormatSpec;
use crate::types::{BinOp, Cell, GcCell, Res};
use crate::{eval_file, eval_raw as eval_str};
use crate::{List, Map, Object, Type};

/// Source code of the standard library (imported under the name 'std')
const STDLIB: &str = include_str!("std.gold");

type ImportCallable = dyn Fn(&str) -> Res<Option<Object>>;

/// Configure the import behavior when evaluating Gold code.
#[derive(Clone, Default)]
pub struct ImportConfig {
    /// If set, unresolved imports will be loaded relative to this path.
    root_path: Option<PathBuf>,

    /// If set, this function will be called to resolve unknown imports.
    ///
    /// It should return Ok(None) to indicate that the path was unknown. In this
    /// case, the importer will attempt to resolve the import to a path if
    /// possible. If the function returns an error, import resolution will be
    /// aborted.
    custom: Option<Rc<ImportCallable>>,
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
    fn resolve(&self, path: &str) -> Res<Object> {
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

#[cfg(feature = "python")]
#[derive(Clone)]
struct PyImportCallable(Rc<ImportCallable>);

#[cfg(feature = "python")]
impl<'s> FromPyObject<'s> for PyImportCallable {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure = move |path: &str| {
                let result = Python::with_gil(|py| {
                    let pypath = PyString::new(py, path);
                    let pyargs = PyTuple::new(py, vec![pypath]);
                    let result = func.call(py, pyargs, None)?;
                    result.extract::<Option<Object>>(py)
                });

                result.map_err(|err| Error::new(Reason::External(err.to_string())))
            };
            Ok(PyImportCallable(Rc::new(closure)))
        } else {
            Err(PyTypeError::new_err(format!(
                "got {}, expected callable",
                obj.get_type().name().unwrap_or("unknown")
            )))
        }
    }
}

#[cfg(feature = "python")]
#[pyclass(unsendable, name = "ImportConfig")]
#[derive(Clone)]
/// Import config that can be constructed by Python code.
pub struct PyImportConfig {
    root_path: Option<String>,
    custom: Option<PyImportCallable>,
}

#[cfg(feature = "python")]
#[pymethods]
impl PyImportConfig {
    #[new]
    #[args(root = "None", custom = "None")]
    fn new(root: Option<String>, custom: Option<PyImportCallable>) -> Self {
        PyImportConfig { root_path: root, custom: custom }
    }
}

#[cfg(feature = "python")]
impl PyImportConfig {
    /// Convert a Python-defined import config object to the native Gold equivalent.
    pub fn to_gold(&self) -> ImportConfig {
        ImportConfig {
            root_path: self.root_path.as_ref().map(PathBuf::from),
            custom: self.custom.as_ref().map(|x| x.0.clone())
        }
    }
}


struct Frame {
    function: CompiledFunction,
    stack: Vec<Object>,
    locals: Vec<Option<Object>>,
    cells: Vec<Cell>,
    enclosed: GcCell<Vec<Cell>>,
    ip: usize,
}

impl Frame {
    fn new(function: CompiledFunction, enclosed: GcCell<Vec<Cell>>) -> Frame {
        let num_locals = function.num_locals;
        let num_cells = function.num_cells;

        let mut cells = Vec::with_capacity(num_cells);
        for _ in 0..num_cells {
            cells.push(Cell::new(None));
        }

        Frame {
            function,
            stack: Vec::new(),
            locals: vec![None; num_locals],
            cells,
            enclosed,
            ip: 0,
        }
    }

    fn next_instruction(&mut self) -> Instruction {
        self.ip += 1;
        self.function.code[self.ip - 1]
    }
}

pub struct Vm<'a> {
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

    pub fn eval(&mut self, function: CompiledFunction) -> Res<Object> {
        self.frames.push(Frame::new(function, GcCell::new(vec![])));
        self.fp = 0;
        self.push(Object::new_map());
        self.push(Object::new_list());
        self.eval_impl()
    }

    pub fn eval_with_args(
        &mut self,
        function: CompiledFunction,
        enclosed: GcCell<Vec<Cell>>,
        args: &List,
        kwargs: Option<&Map>,
    ) -> Res<Object> {
        self.frames.push(Frame::new(function, enclosed));
        self.fp = 0;
        self.push(
            kwargs
                .cloned()
                .map(Object::from)
                .unwrap_or_else(|| Object::new_map()),
        );
        self.push(Object::from(args.clone()));
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
            let other = self.frames[fp].function.trace.error(self.frames[fp].ip - 1);
            err = err.add_locations(other);
        }
        err
    }

    fn eval_impl(&mut self) -> Res<Object> {
        loop {
            let instruction = self.cur_frame().next_instruction();
            match instruction {
                Instruction::LoadConst(i) => {
                    let obj = self.cur_frame().function.constants[i].clone();
                    self.push(obj);
                }

                Instruction::LoadLocal(i) => {
                    let obj = self.cur_frame().locals[i].as_ref().unwrap().clone();
                    self.push(obj);
                }

                Instruction::LoadCell(i) => {
                    let cell = &self.cur_frame().cells[i];
                    let obj: Object = cell.borrow().as_ref().unwrap().clone();
                    self.push(obj);
                }

                Instruction::LoadEnclosed(i) => {
                    let obj = {
                        let e = self.cur_frame().enclosed.borrow();
                        let f = e[i].borrow();
                        f.as_ref().unwrap().clone()
                    };
                    self.push(obj);
                }

                Instruction::LoadFunc(i) => {
                    let func = self.cur_frame().function.functions[i].clone();
                    let obj = Object::new_func(func);
                    self.push(obj);
                }

                Instruction::LoadBuiltin(i) => self.push(Object::new_func(BUILTINS.1[i].clone())),

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
                    self.cur_frame().locals[i] = Some(obj);
                }

                Instruction::StoreCell(i) => {
                    let obj = self.pop();
                    let cell = &self.cur_frame().cells[i];
                    *cell.borrow_mut() = Some(obj);
                }

                Instruction::DestroyLocal(i) => {
                    self.cur_frame().locals[i] = None;
                }

                Instruction::DestroyCell(i) => {
                    let cell = &mut self.cur_frame().cells[i];
                    *cell = Cell::new(None);
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

                    if let Some(f) = func.get_native_callable() {
                        let x = args.get_list().ok_or_else(|| Internal::ArgsNotList.err())?;
                        let y = kwargs.get_map().ok_or_else(|| Internal::KwargsNotMap.err())?;
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
                        None => return Err(self.err().with_reason(Unpack::TypeMismatch(
                            BindingType::List,
                            obj.type_of(),
                        ))),
                        Some(l) => {
                            if l.len() < len {
                                return Err(self.err().with_reason(Unpack::ListTooShort));
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
                    self.push(Object::from(!obj.truthy()));
                }

                Instruction::FormatWithSpec(i) => {
                    let obj = self.pop();
                    let result = Object::from(
                        obj.format(&self.cur_frame().function.fmt_specs[i])
                            .map_err(|e| e.with_locations(self.err()))?,
                    );
                    self.push(result);
                }

                Instruction::FormatWithDefault => {
                    let obj = self.pop();
                    let result = Object::from(
                        obj.format(&FormatSpec::default())
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
                        .map(Object::from)?;
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
                        .map(Object::from)?;
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
                        .map(|x| Object::from(!x))?;
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
                        .map(|x| Object::from(!x))?;
                    self.push(res);
                }

                Instruction::Equal => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(Object::from(lhs.user_eq(&rhs)));
                }

                Instruction::NotEqual => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(Object::from(!lhs.user_eq(&rhs)));
                }

                Instruction::Contains => {
                    let rhs = self.pop();
                    let lhs = self.pop();
                    self.push(Object::from(
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
                    self.push(Object::new_iterator(&obj).map_err(|e| e.with_locations(self.err()))?);
                }

                Instruction::NewString => {
                    self.push(Object::from(""));
                }

                Instruction::PushToList => {
                    let obj = self.pop();
                    self.peek().push(obj)?;
                }

                Instruction::PushToMap => {
                    let value = self.pop();
                    let key = self.pop();
                    self.peek()
                        .insert(key, value)
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
                        .ok_or_else(|| Internal::DelKeyNotMap.err())?;
                    l.remove(&key);
                }

                Instruction::PushCellToClosure(i) => {
                    let cell = self.cur_frame().cells[i].clone();
                    self.peek().push_cell(cell)?;
                }

                Instruction::PushEnclosedToClosure(i) => {
                    let cell = {
                        let cells = self.cur_frame().enclosed.borrow();
                        cells[i].clone()
                    };
                    self.peek().push_cell(cell)?;
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
                            .ok_or_else(|| Internal::IndexNotList.err())?;
                        l.get(i).ok_or_else(|| Internal::IndexOutOfBounds.err())?.clone()
                    };
                    self.push(obj);
                }

                Instruction::IntIndexLAndJump { index, jump } => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_list()
                            .ok_or_else(|| Internal::IndexNotList.err())?;
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
                            .ok_or_else(|| Internal::IndexNotList.err())?;
                        let i = (l.len() - root_back).max(root_front) + index;
                        l.get(i).ok_or_else(|| Internal::IndexOutOfBounds.err())?.clone()
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
                            .ok_or_else(|| Internal::IndexNotList.err())?;
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
                                Object::from(l[start..end].to_vec())
                            } else {
                                Object::new_list()
                            }
                        })
                        .ok_or_else(|| Internal::IndexNotList.err())?;
                    self.push(obj);
                }

                Instruction::IntIndexM(key) => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_map()
                            .ok_or_else(|| Internal::IndexNotMap.err())?;
                        l.get(&key).ok_or_else(|| self.err())?.clone()
                    };
                    self.push(obj);
                }

                Instruction::IntIndexMAndJump { key, jump } => {
                    let obj = {
                        let l = self
                            .peek()
                            .get_map()
                            .ok_or_else(|| Internal::IndexNotMap.err())?;
                        l.get(&key).cloned()
                    };

                    if let Some(x) = obj {
                        self.push(x);
                        self.cur_frame().ip += jump;
                    }
                }

                Instruction::IntPushToKwargs(key) => {
                    let value = self.pop();
                    self.peek_back().insert_key(key, value)?;
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

#[cfg(test)]
mod tests {
    use crate::types::{BinOp, UnOp, Key, Res};
    use crate::error::{Action, BindingType, Error, Reason, Span, TypeMismatch, Types, Unpack};
    use crate::{eval_raw, Object, Type};

    fn eval(input: &str) -> Res<Object> {
        eval_raw(input).map_err(Error::unrender)
    }

    fn eval_errstr(input: &str) -> Option<String> {
        eval_raw(input)
            .err()
            .map(|x| x.render(Some(input)).rendered().map(str::to_owned))
            .flatten()
    }

    trait KeyAble {
        fn key(self) -> Key;
    }

    impl<U> KeyAble for U
    where
        U: AsRef<str>,
    {
        fn key(self) -> Key {
            Key::new(self)
        }
    }

    macro_rules! assert_seq {
        ($x:expr , $y:expr $(,)?) => {
            assert_eq!($x, Ok($y))
        };
    }

    #[test]
    fn booleans_and_null() {
        assert_seq!(eval("true"), Object::from(true));
        assert_seq!(eval("false"), Object::from(false));
        assert_seq!(eval("null"), Object::null());
    }

    #[test]
    fn integers() {
        assert_seq!(eval("1"), Object::from(1));
        assert_seq!(eval("-1"), Object::from(-1));
        assert_seq!(eval("+1"), Object::from(1));
    }

    #[test]
    fn floats() {
        assert_seq!(eval("2."), Object::from(2.0));
        assert_seq!(eval("1.2"), Object::from(1.2));
        assert_seq!(eval("-3e1"), Object::from(-30.0));
        assert_seq!(eval("+4e-1"), Object::from(0.4));
        assert_seq!(eval("5e+1"), Object::from(50.0));
    }

    #[test]
    fn strings() {
        assert_seq!(eval("\"\""), Object::new_str_interned(""));
        assert_seq!(eval("\"simsalabim\""), Object::new_str_interned("simsalabim"));
        assert_seq!(
            eval("\"simsalabim ${-1} abracadabra\""),
            Object::new_str_natural("simsalabim -1 abracadabra")
        );
        assert_seq!(
            eval("\"simsalabim ${0} abracadabra\""),
            Object::new_str_natural("simsalabim 0 abracadabra")
        );
        assert_seq!(
            eval("\"simsalabim ${1} abracadabra\""),
            Object::new_str_natural("simsalabim 1 abracadabra")
        );
        assert_seq!(
            eval("\"simsalabim ${9223372036854775807} abracadabra\""),
            Object::new_str_natural("simsalabim 9223372036854775807 abracadabra")
        );
        assert_seq!(
            eval("\"simsalabim ${9223372036854776000} abracadabra\""),
            Object::new_str_natural("simsalabim 9223372036854776000 abracadabra")
        );
    }

    #[test]
    fn lists() {
        assert_seq!(eval("[]"), Object::new_list());

        assert_seq!(eval("[1]"), Object::from(vec![
            Object::from(1),
        ]));

        assert_seq!(eval("[1, 2, false]"), Object::from(vec![
            Object::from(1),
            Object::from(2),
            Object::from(false),
        ]));

        assert_seq!(eval("[1, 2, 3, 4, 5]"), (1..6).map(Object::from).collect());

        assert_seq!(eval("[1, false, \"dingbob\", 2.2, null]"), Object::from(vec![
            Object::from(1),
            Object::from(false),
            Object::new_str_interned("dingbob"),
            Object::from(2.2),
            Object::null(),
        ]));
    }

    #[test]
    fn maps() {
        assert_seq!(eval("{}"), Object::new_map());

        assert_seq!(
            eval("{a: -1, b: true, c: \"\", d: 3.14, e: null}"),
            Object::from(vec![
                ("a", Object::from(-1)),
                ("b", Object::from(true)),
                ("c", Object::new_str_interned("")),
                ("d", Object::from(3.14)),
                ("e", Object::null()),
            ])
        );

        assert_seq!(
            eval("{$\"a\": 1}"),
            Object::from(vec![("a", Object::from(1)),])
        );

        assert_seq!(
            eval("{$\"abcdefghijklmnopqrstuvwxyz\": 1}"),
            Object::from(vec![("abcdefghijklmnopqrstuvwxyz", Object::from(1)),])
        );
    }

    #[test]
    fn let_bindings() {
        assert_seq!(eval("let a = 1 in a"), Object::from(1));
        assert_seq!(eval("let a = 1 let b = a in b"), Object::from(1));
        assert_seq!(eval("let a = 1 let b = a in a"), Object::from(1));

        assert_seq!(
            eval("let a = 1 let b = \"zomg\" in [a, b]"),
            Object::from(vec![Object::from(1), Object::new_str_interned("zomg"),])
        );

        assert_seq!(
            eval("let a = 1 let b = let a = 2 in a in [a, b]"),
            (1..3).map(Object::from).collect()
        );

        assert_seq!(
            eval("let a = 1 let b = a let a = 2 in [a, b]"),
            Object::from(vec![Object::from(2), Object::from(1),])
        );

        assert!(eval("let a = 1 let b = a in y").is_err());
    }

    #[test]
    fn list_bindings() {
        assert_seq!(eval("let [a] = [1] in a"), Object::from(1));
        assert_seq!(eval("let [a, ...] = [1] in a"), Object::from(1));
        assert_seq!(eval("let [a, ...] = [1, 2, 3] in a"), Object::from(1));
        assert_seq!(eval("let [_, a, ...] = [1, 2, 3] in a"), Object::from(2));
        assert_seq!(eval("let [_, _, a, ...] = [1, 2, 3] in a"), Object::from(3));
        assert_seq!(eval("let [_, _, a] = [1, 2, 3] in a"), Object::from(3));

        assert_seq!(
            eval("let [...a] = [1, 2, 3] in a"),
            (1..4).map(Object::from).collect()
        );
        assert_seq!(
            eval("let [...a, _] = [1, 2, 3] in a"),
            (1..3).map(Object::from).collect()
        );
        assert_seq!(
            eval("let [...a, _, _] = [1, 2, 3] in a"),
            Object::from(vec![Object::from(1)])
        );
        assert_seq!(
            eval("let [_, ...a, _] = [1, 2, 3] in a"),
            Object::from(vec![Object::from(2)])
        );

        assert_seq!(
            eval("let [_, ...a, _, _] = [1, 2, 3] in a"),
            Object::new_list(),
        );

        assert_seq!(eval("let [..., a] = [1] in a"), Object::from(1));
        assert_seq!(eval("let [..., _, a] = [1, 2] in a"), Object::from(2));
        assert_seq!(eval("let [..., a=1] = [2] in a"), Object::from(2));
        assert_seq!(eval("let [..., a=1] = [] in a"), Object::from(1));
        assert_seq!(eval("let [...a, _=1] = [2] in a"), Object::new_list());

        assert_seq!(eval("let [a = 1] = [] in a"), Object::from(1));
        assert_seq!(eval("let [b, a = 1] = [2] in b"), Object::from(2));
        assert_seq!(eval("let [b, a = 1] = [2] in a"), Object::from(1));
        assert_seq!(eval("let [b = 3, a = 1] = [2] in a"), Object::from(1));
        assert_seq!(eval("let [b = 3, a = 1] = [2] in b"), Object::from(2));

        assert!(eval("let [x] = [1, 2, 3] in x").is_err());
        assert!(eval("let [x, y, z, a, ...] = [1, 2, 3] in x").is_err());
        assert!(eval("let [x, ..., y, z, a] = [1, 2, 3] in x").is_err());
        assert!(eval("let [x] = [] in x").is_err());
        assert!(eval("let [x, y = 1] = [] in x").is_err());
        assert!(eval("let [x = 1, y] = [] in x").is_err());

        assert_seq!(
            eval("let [a,b] = [1,2] in {a: a, b: b}"),
            Object::from(vec![("a", Object::from(1)), ("b", Object::from(2))])
        );

        assert_seq!(
            eval("let [a,[b]] = [1,[2]] in {a: a, b: b}"),
            Object::from(vec![("a", Object::from(1)), ("b", Object::from(2))])
        );

        assert_seq!(
            eval("let [a, b = 1, ...c] = [2] in [a, b, c]"),
            Object::from(vec![Object::from(2), Object::from(1), Object::new_list()])
        );
    }

    #[test]
    fn map_bindings() {
        assert_seq!(eval("let {a} = {a: 1} in a"), Object::from(1));
        assert_seq!(eval("let {a as b} = {a: 1} in b"), Object::from(1));
        assert_seq!(eval("let {a as a} = {a: 1} in a"), Object::from(1));

        assert_seq!(eval("let {a, ...x} = {a: 1} in a"), Object::from(1));
        assert_seq!(eval("let {a, ...x} = {a: 1} in x"), Object::new_map());
        assert_seq!(
            eval("let {...x} = {a: 1} in x"),
            Object::from(vec![("a", Object::from(1))])
        );
        assert_seq!(
            eval("let {a, ...x} = {a: 1, b: 2} in x"),
            Object::from(vec![("b", Object::from(2))])
        );
        assert_seq!(eval("let {a, ...x} = {a: 1, b: 2} in a"), Object::from(1));

        assert_seq!(eval("let {a = 1} = {} in a"), Object::from(1));
        assert_seq!(eval("let {a as b = 1} = {} in b"), Object::from(1));

        assert!(eval("let {a} = {} in a").is_err());
        assert!(eval("let {a} = {b: 1} in a").is_err());
    }

    #[test]
    fn function_bindings() {
        assert_seq!(
            eval(concat!(
                "let a = fn (x, [y, z]) x + y + z\n",
                "in a(1, [2, 3])"
            )),
            Object::from(6)
        );

        assert_seq!(
            eval(concat!("let f = fn ([y = 1]) y\n", "in f([])")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!(
                "let q = 1\n",
                "let f = fn ([y = q]) y\n",
                "in f([])"
            )),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!(
                "let f = fn (q) fn ([y = q]) y\n",
                "let q = 1\n",
                "in f(2)([])"
            )),
            Object::from(2)
        );

        assert_seq!(
            eval(concat!(
                "let f = fn (x; y, z) x + y + z\n",
                "in f(1, y: 2, z: 3)"
            )),
            Object::from(6)
        );

        assert_seq!(
            eval(concat!("let f = fn (; y=1) y\n", "in f()")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!("let q = 1\n", "let f = fn (; y=q) y\n", "in f()")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!(
                "let f = fn (q) fn (; y=q) y\n",
                "let q = 1\n",
                "in f(2)()"
            )),
            Object::from(2)
        );

        assert_seq!(
            eval(concat!(
                "let f = fn (x, y=15; z=200) [x,y,z]\n",
                "in [f(1), f(1,2), f(1,z:100), f(1,2,z:100)]"
            )),
            Object::from(vec![
                Object::from(vec![Object::from(1), Object::from(15), Object::from(200)]),
                Object::from(vec![Object::from(1), Object::from(2), Object::from(200)]),
                Object::from(vec![Object::from(1), Object::from(15), Object::from(100)]),
                Object::from(vec![Object::from(1), Object::from(2), Object::from(100)]),
            ])
        );

        assert_seq!(
            eval(concat!(
                "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
                "in dest()"
            )),
            Object::from(vec![Object::new_list(), Object::new_map(),])
        );

        assert_seq!(
            eval(concat!(
                "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
                "in dest(1, 2)"
            )),
            Object::from(vec![(1..3).map(Object::from).collect(), Object::new_map()])
        );

        assert_seq!(
            eval(concat!(
                "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
                "in dest(x: 1, y: 2)"
            )),
            Object::from(vec![
                Object::new_list(),
                Object::from(vec![("x", Object::from(1)), ("y", Object::from(2))]),
            ])
        );

        assert_seq!(
            eval(concat!(
                "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
                "in dest(1, 2, x: 3, y: 4)"
            )),
            Object::from(vec![
                (1..3).map(Object::from).collect(),
                Object::from(vec![("x", Object::from(3)), ("y", Object::from(4))]),
            ])
        );

        assert_seq!(
            eval(concat!(
                "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
                "let args = [1, 2, 3]\n",
                "let kwargs = {x: 4, y: 5, z: 6}\n",
                "in dest(0, ...args, 5, a: 8, ...kwargs, c: 10, z: 12)"
            )),
            Object::from(vec![
                Object::from(vec![
                    Object::from(0),
                    Object::from(1),
                    Object::from(2),
                    Object::from(3),
                    Object::from(5),
                ]),
                Object::from(vec![
                    ("a", Object::from(8)),
                    ("x", Object::from(4)),
                    ("y", Object::from(5)),
                    ("z", Object::from(12)),
                    ("c", Object::from(10)),
                ]),
            ])
        );

        assert_seq!(eval("(fn {} 1)()"), Object::from(1));
        assert_seq!(eval("(fn {a, b} a + b)(a: 1, b: 2)"), Object::from(3));
        assert_seq!(eval("(fn {a, b=2} a + b)(a: 1, b: 3)"), Object::from(4));
        assert_seq!(eval("(fn {a, b=2} a + b)(a: 1)"), Object::from(3));
    }

    #[test]
    fn deferred() {
        assert_seq!(
            eval(concat!("let a = fn () b\n", "let b = 1\n", "in a()",)),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!(
                "let a = 1\n",
                "in let a = a + 1\n",
                "   let b = fn () a\n",
                "   in [a, b()]"
            )),
            Object::from(vec![Object::from(2), Object::from(2)]),
        );

        assert_seq!(
            eval(concat!(
                "let a = 1\n",
                "in let b = fn () a\n",
                "   let a = a + 1\n",
                "   in [a, b()]"
            )),
            Object::from(vec![Object::from(2), Object::from(2)]),
        );
    }

    #[test]
    fn arithmetic() {
        assert_seq!(eval("1 + 2"), Object::from(3));
        assert_seq!(eval("3 + 2"), Object::from(5));
        assert_seq!(eval("3 + 2 - 5"), Object::from(0));
        assert_seq!(eval("3 - -5"), Object::from(8));
        assert_seq!(eval("2 * 4"), Object::from(8));
        assert_seq!(eval("2.0 * 4"), Object::from(8.0));
        assert_seq!(eval("2 * 4.0"), Object::from(8.0));
        assert_seq!(eval("2 * 4 + 1"), Object::from(9));
        assert_seq!(eval("2 * (4 + 1)"), Object::from(10));
        assert_seq!(eval("3 / 2"), Object::from(1.5));
        assert_seq!(eval("3.0 / 2"), Object::from(1.5));
        assert_seq!(eval("3 / 2.0"), Object::from(1.5));
        assert_seq!(eval("3.0 / 2.0"), Object::from(1.5));
        assert_seq!(eval("3 // 2"), Object::from(1));
        assert_seq!(eval("1 + 2.0"), Object::from(3.0));
        assert_seq!(eval("1.0 + 2"), Object::from(3.0));
        assert_seq!(eval("1.0 + 2.0"), Object::from(3.0));
        assert_seq!(eval("1.0 - 2.0"), Object::from(-1.0));
        assert_seq!(eval("1.0 - 2"), Object::from(-1.0));
        assert_seq!(eval("1 - 2.0"), Object::from(-1.0));
        assert_seq!(eval("1 - 2 + 3"), Object::from(2));
        assert_seq!(eval("2 // 2 * 2"), Object::from(2));
        assert_seq!(eval("2 ^ 2"), Object::from(4));
        assert_seq!(eval("-2 ^ 2"), Object::from(-4));
        assert_seq!(eval("2 ^ 2 ^ 2"), Object::from(16));
        assert_seq!(eval("-2 ^ 2 ^ 2"), Object::from(-16));
        assert_seq!(eval("2 ^ 3 ^ 3"), Object::from(134217728));
        assert_seq!(eval("(2 ^ 3) ^ 3"), Object::from(512));
        assert_seq!(eval("-2 ^ 3 ^ 3"), Object::from(-134217728));
        assert_seq!(eval("(-2 ^ 3) ^ 3"), Object::from(-512));
        assert_seq!(eval("-(2 ^ 3) ^ 3"), Object::from(-512));
        assert_seq!(eval("2 ^ -1"), Object::from(0.5));

        assert_seq!(
            eval("(9999999999999999999999999 + 1) - 9999999999999999999999999"),
            Object::from(1)
        );
        assert_seq!(
            eval("9223372036854775800 + 9223372036854775800 - 9223372036854775800"),
            Object::from(9223372036854775800_i64)
        );
        assert_seq!(
            eval("(-9999999999999999999999999 - 1) + 9999999999999999999999999"),
            Object::from(-1)
        );
    }

    #[test]
    fn compare() {
        assert_seq!(eval("1 < 2"), Object::from(true));
        assert_seq!(eval("1 < 2.0"), Object::from(true));
        assert_seq!(eval("1.0 < 2"), Object::from(true));
        assert_seq!(eval("1.0 < 2.0"), Object::from(true));
        assert_seq!(eval("\"a\" < \"b\""), Object::from(true));

        assert_seq!(eval("1 > 2"), Object::from(false));
        assert_seq!(eval("1 > 2.0"), Object::from(false));
        assert_seq!(eval("1.0 > 2"), Object::from(false));
        assert_seq!(eval("1.0 > 2.0"), Object::from(false));
        assert_seq!(eval("\"a\" > \"b\""), Object::from(false));

        assert_seq!(eval("2 <= 2"), Object::from(true));
        assert_seq!(eval("2 <= 2.0"), Object::from(true));
        assert_seq!(eval("2.0 <= 2"), Object::from(true));
        assert_seq!(eval("2.0 <= 2.0"), Object::from(true));
        assert_seq!(eval("\"a\" <= \"b\""), Object::from(true));

        assert_seq!(eval("1 >= 2"), Object::from(false));
        assert_seq!(eval("1 >= 2.0"), Object::from(false));
        assert_seq!(eval("1.0 >= 2"), Object::from(false));
        assert_seq!(eval("1.0 >= 2.0"), Object::from(false));
        assert_seq!(eval("\"a\" >= \"b\""), Object::from(false));

        assert_seq!(eval("1 == 2"), Object::from(false));
        assert_seq!(eval("2 == 2"), Object::from(true));
        assert_seq!(eval("2.0 == 2.0"), Object::from(true));
        assert_seq!(eval("2 == 2.0"), Object::from(true));
        assert_seq!(eval("2.0 == 2"), Object::from(true));
        assert_seq!(eval("\"a\" == \"b\""), Object::from(false));
        assert_seq!(eval("true == false"), Object::from(false));
        assert_seq!(eval("null == null"), Object::from(true));

        assert_seq!(eval("[] == []"), Object::from(true));
        assert_seq!(eval("[1] == []"), Object::from(false));
        assert_seq!(eval("[1] == [2]"), Object::from(false));
        assert_seq!(eval("[1] == [1]"), Object::from(true));
        assert_seq!(eval("[1] == [1.0]"), Object::from(true));

        assert_seq!(eval("{} == {}"), Object::from(true));
        assert_seq!(eval("{a: 1} == {}"), Object::from(false));
        assert_seq!(eval("{a: 1} == {a: 1}"), Object::from(true));
        assert_seq!(eval("{b: 1} == {a: 1}"), Object::from(false));
        assert_seq!(eval("{a: 1.0} == {a: 1}"), Object::from(true));
        assert_seq!(eval("{a: 2} == {a: 1}"), Object::from(false));
        assert_seq!(eval("{a: 1} == {a: 1, b: 1}"), Object::from(false));
        assert_seq!(eval("{a: 1} == {a: 1, a: 1}"), Object::from(true));

        assert_seq!(eval("[] == {}"), Object::from(false));

        assert_seq!(eval("1 != 2"), Object::from(true));
        assert_seq!(eval("2 != 2"), Object::from(false));
        assert_seq!(eval("2.0 != 2.0"), Object::from(false));
        assert_seq!(eval("2 != 2.0"), Object::from(false));
        assert_seq!(eval("2.0 != 2"), Object::from(false));
        assert_seq!(eval("\"a\" != \"b\""), Object::from(true));
        assert_seq!(eval("true != false"), Object::from(true));
        assert_seq!(eval("null != null"), Object::from(false));

        assert_seq!(eval("[] != []"), Object::from(false));
        assert_seq!(eval("[1] != []"), Object::from(true));
        assert_seq!(eval("[1] != [2]"), Object::from(true));
        assert_seq!(eval("[1] != [1]"), Object::from(false));
        assert_seq!(eval("[1] != [1.0]"), Object::from(false));

        assert_seq!(eval("{} != {}"), Object::from(false));
        assert_seq!(eval("{a: 1} != {}"), Object::from(true));
        assert_seq!(eval("{a: 1} != {a: 1}"), Object::from(false));
        assert_seq!(eval("{b: 1} != {a: 1}"), Object::from(true));
        assert_seq!(eval("{a: 1.0} != {a: 1}"), Object::from(false));
        assert_seq!(eval("{a: 2} != {a: 1}"), Object::from(true));
        assert_seq!(eval("{a: 1} != {a: 1, b: 1}"), Object::from(true));
        assert_seq!(eval("{a: 1} != {a: 1, a: 1}"), Object::from(false));

        assert_seq!(eval("[] != {}"), Object::from(true));
    }

    #[test]
    fn containment() {
        assert_seq!(eval("[1] has 1"), Object::from(true));
        assert_seq!(eval("[1] has 2"), Object::from(false));
        assert_seq!(eval("\"bobloblaw\" has \"bob\""), Object::from(true));
        assert_seq!(eval("\"bobloblaw\" has \"blob\""), Object::from(true));
        assert_seq!(eval("\"bobloblaw\" has \"lobl\""), Object::from(true));
        assert_seq!(eval("\"bobloblaw\" has \"shrimp\""), Object::from(false));
    }

    #[test]
    fn logic() {
        assert_seq!(eval("true and 1"), Object::from(1));
        assert_seq!(eval("false and 1"), Object::from(false));
        assert_seq!(eval("true or 1"), Object::from(true));
        assert_seq!(eval("false or 1"), Object::from(1));
        assert_seq!(eval("null or 1"), Object::from(1));
        assert_seq!(eval("1 or 1"), Object::from(1));
    }

    #[test]
    fn list_concat() {
        assert_seq!(eval("[1, 2] + [3]"), (1..4).map(Object::from).collect());
        assert_seq!(eval("[1, 2] + []"), (1..3).map(Object::from).collect());
        assert_seq!(eval("[] + [3]"), Object::from(vec![Object::from(3)]));

        assert_seq!(
            eval("[...[1, 2], ...[3]]"),
            (1..4).map(Object::from).collect()
        );
        assert_seq!(
            eval("[...[1, 2], ...[]]"),
            (1..3).map(Object::from).collect()
        );
        assert_seq!(eval("[...[1, 2]]"), (1..3).map(Object::from).collect());
        assert_seq!(eval("[...[], ...[3]]"), Object::from(vec![Object::from(3)]));
        assert_seq!(eval("[...[3]]"), Object::from(vec![Object::from(3)]));
    }

    #[test]
    fn map_concat() {
        assert_seq!(
            eval("{a: 1, ...{b: 2, c: 3}, d: 4}"),
            Object::from(vec![
                ("a", Object::from(1)),
                ("b", Object::from(2)),
                ("c", Object::from(3)),
                ("d", Object::from(4)),
            ])
        );

        assert_seq!(
            eval("{a: 1, ...{a: 2, c: 3}, c: 4}"),
            Object::from(vec![("a", Object::from(2)), ("c", Object::from(4)),])
        );
    }

    #[test]
    fn functions() {
        assert_seq!(eval("let f = fn () 1 in f()"), Object::from(1));

        assert_seq!(eval("let a = 1 let f = fn () a in f()"), Object::from(1));

        assert_seq!(
            eval(concat!(
                "let double = fn (x) x + x\n",
                "let applytwice = fn (f,x) f(f(x))\n",
                "in applytwice(double, [1])"
            )),
            Object::from(vec![
                Object::from(1),
                Object::from(1),
                Object::from(1),
                Object::from(1),
            ])
        );

        assert_seq!(
            eval(concat!(
                "let a = 1\n",
                "let b = fn () a\n",
                "let a = 2\n",
                "in b()"
            )),
            Object::from(2)
        );

        assert_seq!(
            eval(concat!("let a = 1\n", "let b = fn (q = a) q\n", "in b()")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!(
                "let a = 1\n",
                "let b = fn (q = a) q\n",
                "let a = 2\n",
                "in b()"
            )),
            Object::from(2)
        );

        assert_seq!(
            eval(concat!(
                "let b = fn () let a = 1 in fn (q = a) q\n",
                "let c = b()\n",
                "in c()"
            )),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!("let a = fn (q, ...x) [q, ...x]\n", "in a(1, 2, 3)")),
            (1..4).map(Object::from).collect()
        );

        assert_seq!(
            eval(concat!("let a = fn (q, p = q) p\n", "in a(1, 2)")),
            Object::from(2)
        );

        assert_seq!(
            eval(concat!("let a = fn (q, p = q) p\n", "in a(1)")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!("let a = fn (; k = 1) k\n", "in a()")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!("let a = fn (; k = 1) k\n", "in a(k: 2)")),
            Object::from(2)
        );

        assert_seq!(
            eval(concat!("let a = fn {k = 1} k\n", "in a()")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!("let a = fn {k = 1} k\n", "in a(k: 2)")),
            Object::from(2)
        );

        assert_seq!(
            eval(concat!("let a = 1\n", "in (fn () fn () a)()()")),
            Object::from(1)
        );

        assert_seq!(
            eval(concat!("let a = 1\n", "in (fn () fn () fn () a)()()()")),
            Object::from(1)
        );
    }

    #[test]
    fn subscripting() {
        assert_seq!(eval("[1, 2, 3][0]"), Object::from(1));
        assert_seq!(eval("[1, 2, 3][1]"), Object::from(2));
        assert_seq!(eval("[1, 2, 3][2]"), Object::from(3));

        assert_seq!(eval("{a: 1, b: 2}.a"), Object::from(1));
        assert_seq!(eval("{a: 1, b: 2}.b"), Object::from(2));
        assert_seq!(eval("{a: 1, b: 2}[\"a\"]"), Object::from(1));
        assert_seq!(eval("{a: 1, b: 2}[\"b\"]"), Object::from(2));
    }

    #[test]
    fn branching() {
        assert_seq!(eval("if true then 1 else 2"), Object::from(1));
    }

    #[test]
    fn branching_in_collections() {
        assert_seq!(
            eval("[if true then 1 else 2, 3]"),
            Object::from(vec![Object::from(1), Object::from(3),])
        );

        assert_seq!(
            eval("[if false then 1 else 2, 3]"),
            Object::from(vec![Object::from(2), Object::from(3),])
        );
    }

    #[test]
    fn conditional_collection_elements() {
        assert_seq!(
            eval("[when true: 1, when false: 2, if true then 3 else 4, 5]"),
            Object::from(vec![Object::from(1), Object::from(3), Object::from(5),])
        );

        assert_seq!(
            eval("{a: if true then 1 else 2, when true: b: 3, when false: c: 4}"),
            Object::from(vec![("a", Object::from(1)), ("b", Object::from(3)),])
        );
    }

    #[test]
    fn iterable_collection_elements() {
        assert_seq!(
            eval("let a = [1, 2, 3] in [for x in a: x + 1]"),
            (2..5).map(Object::from).collect()
        );

        assert_seq!(
            eval("{for [x,y] in [[\"a\", 1], [\"b\", 2]]: $x: y}"),
            Object::from(vec![("a", Object::from(1)), ("b", Object::from(2))])
        );
    }

    #[test]
    fn complex_collection_elements() {
        assert_seq!(
            eval(concat!(
                "let a = [1, 2, 3, 4, 5]\n",
                "in [for x in a: when x < 3: x]"
            )),
            (1..3).map(Object::from).collect()
        );

        assert_seq!(
            eval(concat!(
                "let a = [[1], [2, 3], [4, 5, 6]]\n",
                "in [for x in a: when len(x) > 1: ...x]"
            )),
            (2..7).map(Object::from).collect()
        );

        assert_seq!(
            eval(concat!(
                "let a = [[\"x\",1], [\"y\",2], [\"z\",3]]\n",
                "in {for [x,y] in a: when y != 2: $x: y}"
            )),
            Object::from(vec![("x", Object::from(1)), ("z", Object::from(3)),])
        );
    }

    #[test]
    fn builtins() {
        assert_seq!(eval("len([1, 2])"), Object::from(2));
        assert_seq!(eval("len([])"), Object::from(0));

        assert_seq!(eval("len({})"), Object::from(0));
        assert_seq!(eval("len({a: 1})"), Object::from(1));

        assert_seq!(eval("len(\"\")"), Object::from(0));
        assert_seq!(eval("len(\"abc\")"), Object::from(3));
        assert_seq!(eval("len(\"å\")"), Object::from(1));

        assert_seq!(eval("range(3)"), (0..3).map(Object::from).collect());
        assert_seq!(eval("range(1, 3)"), (1..3).map(Object::from).collect());

        assert_seq!(eval("int(1)"), Object::from(1));
        assert_seq!(eval("int(true)"), Object::from(1));
        assert_seq!(eval("int(false)"), Object::from(0));
        assert_seq!(eval("int(1.2)"), Object::from(1));
        assert_seq!(eval("int(-1.2)"), Object::from(-1));
        assert_seq!(eval("int(\"-3\")"), Object::from(-3));

        assert_seq!(eval("bool(1)"), Object::from(true));
        assert_seq!(eval("bool(0)"), Object::from(false));
        assert_seq!(eval("bool(1.5)"), Object::from(true));
        assert_seq!(eval("bool(0.0)"), Object::from(false));
        assert_seq!(eval("bool(true)"), Object::from(true));
        assert_seq!(eval("bool(false)"), Object::from(false));
        assert_seq!(eval("bool(null)"), Object::from(false));
        assert_seq!(eval("bool([])"), Object::from(true));
        assert_seq!(eval("bool({})"), Object::from(true));

        assert_seq!(eval("str(1)"), Object::from("1"));
        assert_seq!(eval("str(1.2)"), Object::from("1.2"));
        assert_seq!(eval("str(\"delta\")"), Object::from("delta"));
        assert_seq!(eval("str(true)"), Object::from("true"));
        assert_seq!(eval("str(false)"), Object::from("false"));
        assert_seq!(eval("str(null)"), Object::from("null"));

        assert_seq!(eval("float(1)"), Object::from(1.0));
        assert_seq!(eval("float(1.0)"), Object::from(1.0));
        assert_seq!(eval("float(true)"), Object::from(1.0));
        assert_seq!(eval("float(false)"), Object::from(0.0));
        assert_seq!(eval("float(\"1.2\")"), Object::from(1.2));
    }

    macro_rules! loc {
        ($loc:expr, $act:ident) => {
            (Span::from($loc), Action::$act)
        };
    }

    macro_rules! err {
        ($reason:expr, $($locs:expr),*) => {
            Err(Error::new($reason).with_locations_vec(vec![$($locs),*]))
        }
    }

    #[test]
    fn errors() {
        assert_eq!(
            eval("a"),
            err!(Reason::Unbound("a".key()), loc!(0, LookupName))
        );
        assert_eq!(
            eval("let [a] = [] in a"),
            err!(Unpack::ListTooShort, loc!(4..7, Bind))
        );
        assert_eq!(
            eval("let [a] = [1, 2] in a"),
            err!(Unpack::ListTooLong, loc!(4..7, Bind))
        );
        assert_eq!(
            eval("let {a} = {} in a"),
            err!(
                Unpack::KeyMissing("a".key()),
                loc!(5, Bind),
                loc!(4..7, Bind)
            )
        );
        assert_eq!(
            eval("let [a] = 1 in a"),
            err!(
                Unpack::TypeMismatch(BindingType::List, Type::Integer),
                loc!(4..7, Bind)
            )
        );
        assert_eq!(
            eval("let {a} = true in a"),
            err!(
                Unpack::TypeMismatch(BindingType::Map, Type::Boolean),
                loc!(4..7, Bind)
            )
        );
        assert_eq!(
            eval("[...1]"),
            err!(TypeMismatch::SplatList(Type::Integer), loc!(4, Splat))
        );
        assert_eq!(
            eval("[for x in 1: x]"),
            err!(TypeMismatch::Iterate(Type::Integer), loc!(10, Iterate))
        );
        assert_eq!(
            eval("{$null: 1}"),
            err!(TypeMismatch::MapKey(Type::Null), loc!(2..6, Assign))
        );
        assert_eq!(
            eval("{...[]}"),
            err!(TypeMismatch::SplatMap(Type::List), loc!(4..6, Splat))
        );
        assert_eq!(
            eval("{for x in 2.2: a: x}"),
            err!(TypeMismatch::Iterate(Type::Float), loc!(10..13, Iterate))
        );
        assert_eq!(
            eval("(fn (...x) 1)(...true)"),
            err!(TypeMismatch::SplatArg(Type::Boolean), loc!(17..21, Splat))
        );
        assert_eq!(
            eval("1 + true"),
            err!(
                TypeMismatch::BinOp(Type::Integer, Type::Boolean, BinOp::Add),
                loc!(2, Evaluate)
            )
        );
        assert_eq!(
            eval("\"t\" - 9"),
            err!(
                TypeMismatch::BinOp(Type::String, Type::Integer, BinOp::Subtract),
                loc!(4, Evaluate)
            )
        );
        assert_eq!(
            eval("[] * 9"),
            err!(
                TypeMismatch::BinOp(Type::List, Type::Integer, BinOp::Multiply),
                loc!(3, Evaluate)
            )
        );
        assert_eq!(
            eval("9 / {}"),
            err!(
                TypeMismatch::BinOp(Type::Integer, Type::Map, BinOp::Divide),
                loc!(2, Evaluate)
            )
        );
        assert_eq!(
            eval("null // {}"),
            err!(
                TypeMismatch::BinOp(Type::Null, Type::Map, BinOp::IntegerDivide),
                loc!(5..7, Evaluate)
            )
        );
        assert_eq!(
            eval("null < true"),
            err!(
                TypeMismatch::BinOp(Type::Null, Type::Boolean, BinOp::Less),
                loc!(5, Evaluate)
            )
        );
        assert_eq!(
            eval("1 > \"\""),
            err!(
                TypeMismatch::BinOp(Type::Integer, Type::String, BinOp::Greater),
                loc!(2, Evaluate)
            )
        );
        assert_eq!(
            eval("[] <= 2.1"),
            err!(
                TypeMismatch::BinOp(Type::List, Type::Float, BinOp::LessEqual),
                loc!(3..5, Evaluate)
            )
        );
        assert_eq!(
            eval("{} >= false"),
            err!(
                TypeMismatch::BinOp(Type::Map, Type::Boolean, BinOp::GreaterEqual),
                loc!(3..5, Evaluate)
            )
        );
        assert_eq!(
            eval("1 has 2"),
            err!(
                TypeMismatch::BinOp(Type::Integer, Type::Integer, BinOp::Contains),
                loc!(2..5, Evaluate)
            )
        );
        assert_eq!(
            eval("\"${[]}\""),
            err!(TypeMismatch::Interpolate(Type::List), loc!(3..5, Format))
        );
        assert_eq!(
            eval("\"${{}}\""),
            err!(TypeMismatch::Interpolate(Type::Map), loc!(3..5, Format))
        );
        assert_eq!(
            eval("-null"),
            err!(
                TypeMismatch::UnOp(Type::Null, UnOp::ArithmeticalNegate),
                loc!(0, Evaluate)
            )
        );
        assert_eq!(
            eval("null[2]"),
            err!(
                TypeMismatch::BinOp(Type::Null, Type::Integer, BinOp::Index),
                loc!(4..7, Evaluate)
            )
        );
        assert_eq!(
            eval("2[null]"),
            err!(
                TypeMismatch::BinOp(Type::Integer, Type::Null, BinOp::Index),
                loc!(1..7, Evaluate)
            )
        );
        assert_eq!(
            eval("(2).x"),
            err!(
                TypeMismatch::BinOp(Type::Integer, Type::String, BinOp::Index),
                loc!(3, Evaluate)
            )
        );
        assert_eq!(
            eval("{a: 1}.b"),
            err!(Reason::Unassigned("b".key()), loc!(6, Evaluate))
        );
        assert_eq!(
            eval("{a: 1}[\"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\"]"),
            err!(
                Reason::Unassigned("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".key()),
                loc!(6..66, Evaluate)
            )
        );
        assert_eq!(
            eval("[]()"),
            err!(TypeMismatch::Call(Type::List), loc!(2..4, Evaluate))
        );
        assert_eq!(
            eval("true(1)"),
            err!(TypeMismatch::Call(Type::Boolean), loc!(4..7, Evaluate))
        );

        assert_eq!(
            eval("range()"),
            err!(
                TypeMismatch::ArgCount {
                    low: 1,
                    high: 2,
                    received: 0
                },
                loc!(5..7, Evaluate)
            )
        );
        assert_eq!(
            eval("range(1, 2, 3)"),
            err!(
                TypeMismatch::ArgCount {
                    low: 1,
                    high: 2,
                    received: 3
                },
                loc!(5..14, Evaluate)
            )
        );

        assert_eq!(
            eval("len(1)"),
            err!(
                TypeMismatch::ExpectedPosArg {
                    index: 0,
                    allowed: Types::Three(Type::String, Type::List, Type::Map),
                    received: Type::Integer,
                },
                loc!(3..6, Evaluate)
            )
        );

        assert_eq!(
            eval("len(true)"),
            err!(
                TypeMismatch::ExpectedPosArg {
                    index: 0,
                    allowed: Types::Three(Type::String, Type::List, Type::Map),
                    received: Type::Boolean
                },
                loc!(3..9, Evaluate)
            )
        );

        assert!(eval_errstr("a").is_some_and(|x| x.contains("\na\n^\n")));
        assert!(eval_errstr("\n\na\n").is_some_and(|x| x.contains("\na\n^\n")));
        assert!(eval_errstr("  a  \n").is_some_and(|x| x.contains("\n  a  \n  ^\n")));
        assert!(eval_errstr("\n  a  \n").is_some_and(|x| x.contains("\n  a  \n  ^\n")));
        assert!(
            eval_errstr("\n  bingbong  \n").is_some_and(|x| x.contains("\n  bingbong  \n  ^^^^^^^^\n"))
        );

        assert!(eval_errstr(concat!(
            "let f = fn (x) x + 1\n",
            "let g = fn (x) f(x)\n",
            "let h = fn (x) g(x)\n",
            "in h(null)",
        ))
        .is_some_and(
            |x| x.contains(concat!("let f = fn (x) x + 1\n", "                 ^",))
                && x.contains(concat!("let g = fn (x) f(x)\n", "                ^^^",))
                && x.contains(concat!("let h = fn (x) g(x)\n", "                ^^^",))
                && x.contains(concat!("in h(null)\n", "    ^^^^^",))
        ));
    }
}

#[cfg(test)]
mod examples {
    use std::env;
    use std::path::PathBuf;
    use crate::{Object, Error, eval_file};
    use crate::types::Res;

    fn eval(example: &str) -> Res<Object> {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.pop();
        path.push("examples");
        path.push(example);
        eval_file(&path).map_err(Error::unrender)
    }

    macro_rules! assert_seq {
        ($x:expr , $y:expr $(,)?) => {
            assert_eq!($x, Ok($y))
        };
    }

    #[test]
    fn dh_books() {
        assert_seq!(
            eval("dh-books.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("category", Object::from("nonfiction")),
                    ("department", Object::from("books")),
                    ("publisher", Object::from("O'Reilly Media")),
                    ("title", Object::from("Microservices for Java Developers"))
                ]),
                Object::from(vec![
                    ("category", Object::from("nonfiction")),
                    ("department", Object::from("books")),
                    ("publisher", Object::from("Addison Wesley")),
                    ("title", Object::from("The Go Programming Language"))
                ]),
                Object::from(vec![
                    ("category", Object::from("nonfiction")),
                    ("department", Object::from("books")),
                    ("publisher", Object::from("O'Reilly Media")),
                    ("title", Object::from("Parallel and Concurrent Programming in Haskell"))
                ]),
            ]),
        );
    }

    #[test]
    fn dh_definitions() {
        assert_seq!(
            eval("dh-definitions.gold"),
            Object::from(vec![
                ("home", Object::new_str_natural("/home/bill")),
                ("privateKey", Object::from("/home/bill/.ssh/id_ed25519")),
                ("publicKey", Object::from("/home/bill/.ssh/id_ed25519.pub")),
            ]),
        );
    }

    #[test]
    fn dh_employees() {
        assert_seq!(
            eval("dh-employees.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("age", Object::from(23)),
                    ("name", Object::from("John Doe")),
                    ("position", Object::from(vec![
                        ("department", Object::from("Data Platform")),
                        ("title", Object::from("Software Engineer")),
                    ]))
                ]),
                Object::from(vec![
                    ("age", Object::from(24)),
                    ("name", Object::from("Alice Smith")),
                    ("position", Object::from(vec![
                        ("department", Object::from("Data Platform")),
                        ("title", Object::from("Software Engineer")),
                    ]))
                ]),
            ]),
        )
    }

    #[test]
    fn dh_filter() {
        assert_seq!(
            eval("dh-filter.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("name", Object::from("Alice")),
                    ("age", Object::from(24)),
                    ("admin", Object::from(true)),
                ]),
                Object::from(vec![
                    ("name", Object::from("Bob")),
                    ("age", Object::from(49)),
                    ("admin", Object::from(true)),
                ]),
            ]),
        );
    }

    #[test]
    fn dh_functions() {
        assert_seq!(
            eval("dh-functions.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/bill")),
                    ("privateKey", Object::from("/home/bill/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/bill/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/jane")),
                    ("privateKey", Object::from("/home/jane/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/jane/.ssh/id_ed25519.pub")),
                ]),
            ]),
        );
    }

    #[test]
    fn dh_generate() {
        assert_seq!(
            eval("dh-generate.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build0")),
                    ("privateKey", Object::from("/home/build0/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build0/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build1")),
                    ("privateKey", Object::from("/home/build1/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build1/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build2")),
                    ("privateKey", Object::from("/home/build2/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build2/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build3")),
                    ("privateKey", Object::from("/home/build3/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build3/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build4")),
                    ("privateKey", Object::from("/home/build4/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build4/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build5")),
                    ("privateKey", Object::from("/home/build5/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build5/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build6")),
                    ("privateKey", Object::from("/home/build6/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build6/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build7")),
                    ("privateKey", Object::from("/home/build7/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build7/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build8")),
                    ("privateKey", Object::from("/home/build8/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build8/.ssh/id_ed25519.pub")),
                ]),
                Object::from(vec![
                    ("home", Object::new_str_natural("/home/build9")),
                    ("privateKey", Object::from("/home/build9/.ssh/id_ed25519")),
                    ("publicKey", Object::from("/home/build9/.ssh/id_ed25519.pub")),
                ]),
            ]),
        );
    }

    #[test]
    fn dh_hello_world() {
        assert_seq!(
            eval("dh-hello-world.gold"),
            Object::from(vec![
                ("home", Object::from("/home/bill")),
                ("privateKey", Object::from("/home/bill/.ssh/id_ed25519")),
                ("publicKey", Object::from("/home/bill/.ssh/id_ed25519.pub")),
            ]),
        );
    }

    #[test]
    fn dh_servers() {
        assert_seq!(
            eval("dh-servers.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("cpus", Object::from(1)),
                    ("gigabytesOfRAM", Object::from(1)),
                    ("hostname", Object::from("eu-west.example.com")),
                    ("terabytesOfDisk", Object::from(1)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(64)),
                    ("gigabytesOfRAM", Object::from(256)),
                    ("hostname", Object::from("us-east.example.com")),
                    ("terabytesOfDisk", Object::from(16)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(64)),
                    ("gigabytesOfRAM", Object::from(256)),
                    ("hostname", Object::from("ap-northeast.example.com")),
                    ("terabytesOfDisk", Object::from(16)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(8)),
                    ("gigabytesOfRAM", Object::from(16)),
                    ("hostname", Object::from("us-west.example.com")),
                    ("terabytesOfDisk", Object::from(4)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(1)),
                    ("gigabytesOfRAM", Object::from(1)),
                    ("hostname", Object::from("sa-east.example.com")),
                    ("terabytesOfDisk", Object::from(1)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(64)),
                    ("gigabytesOfRAM", Object::from(256)),
                    ("hostname", Object::from("ca-central.example.com")),
                    ("terabytesOfDisk", Object::from(16)),
                ]),
            ]),
        );
    }

    #[test]
    fn dh_servers_2() {
        assert_seq!(
            eval("dh-servers-2.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("cpus", Object::from(1)),
                    ("gigabytesOfRAM", Object::from(1)),
                    ("hostname", Object::from("eu-west.example.com")),
                    ("terabytesOfDisk", Object::from(1)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(64)),
                    ("gigabytesOfRAM", Object::from(256)),
                    ("hostname", Object::from("us-east.example.com")),
                    ("terabytesOfDisk", Object::from(16)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(64)),
                    ("gigabytesOfRAM", Object::from(256)),
                    ("hostname", Object::from("ap-northeast.example.com")),
                    ("terabytesOfDisk", Object::from(16)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(8)),
                    ("gigabytesOfRAM", Object::from(16)),
                    ("hostname", Object::from("us-west.example.com")),
                    ("terabytesOfDisk", Object::from(4)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(1)),
                    ("gigabytesOfRAM", Object::from(1)),
                    ("hostname", Object::from("sa-east.example.com")),
                    ("terabytesOfDisk", Object::from(1)),
                ]),
                Object::from(vec![
                    ("cpus", Object::from(64)),
                    ("gigabytesOfRAM", Object::from(256)),
                    ("hostname", Object::from("ca-central.example.com")),
                    ("terabytesOfDisk", Object::from(16)),
                ]),
            ]),
        );
    }

    #[test]
    fn dh_users() {
        assert_seq!(
            eval("dh-users.gold"),
            Object::from(vec![
                Object::from(vec![
                    ("name", Object::from("Alice")),
                    ("age", Object::from(24)),
                    ("admin", Object::from(true)),
                ]),
                Object::from(vec![
                    ("name", Object::from("Bob")),
                    ("age", Object::from(49)),
                    ("admin", Object::from(true)),
                ]),
                Object::from(vec![
                    ("name", Object::from("Carlo")),
                    ("age", Object::from(20)),
                    ("admin", Object::from(false)),
                ]),
            ]),
        );
    }

    #[test]
    fn fibonacci() {
        assert_seq!(eval("fibonacci.gold"), Object::from(13));
    }

    #[test]
    fn fibonacci_recursive() {
        assert_seq!(eval("fibonacci-recursive.gold"), Object::from(13));
    }

    #[test]
    fn import() {
        assert_seq!(eval("import.gold"), Object::from(3));
    }
}
