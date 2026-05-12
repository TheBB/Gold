use crate::ast::high::{
    ArgElement, Binding, Expr, File, ListBinding, ListBindingElement, ListElement, MapBinding,
    MapBindingElement, MapElement, StringElement, TopLevel, Transform,
};
use crate::error::{Error, Span, Tagged};
use crate::formatting::{
    AlignSpec, FloatFormatType, FormatSpec, FormatType, GroupingSpec, IntegerFormatType, SignSpec,
    StringAlignSpec, UppercaseSpec,
};
use crate::types::{BinOp, EagerOp, LogicOp, UnOp};
use crate::Object;

// ── Public API ────────────────────────────────────────────────────────────────

/// Options controlling pprint output format.
pub struct PprintOptions {
    /// Whether to include span offsets in the output.
    pub show_spans: bool,
    /// If set, truncate string values longer than this many characters.
    pub max_str_len: Option<usize>,
}

impl Default for PprintOptions {
    fn default() -> Self {
        Self { show_spans: false, max_str_len: None }
    }
}

/// Render a parse result as a human-readable tree string.
pub fn pprint(result: &Result<File, Error>, opts: &PprintOptions) -> String {
    let mut pp = Pp { opts, out: Vec::new() };
    pp.result(result, 0);
    pp.out.join("\n")
}

// ── Internal renderer ─────────────────────────────────────────────────────────

struct Pp<'a> {
    opts: &'a PprintOptions,
    out: Vec<String>,
}

impl<'a> Pp<'a> {
    fn emit(&mut self, indent: usize, text: impl Into<String>) {
        let s = text.into();
        if indent == 0 {
            self.out.push(s);
        } else {
            self.out.push(format!("{}{}", "  ".repeat(indent), s));
        }
    }

    fn span_str(&self, span: Span) -> String {
        if self.opts.show_spans {
            format!(" [{}..{}]", span.offset(), span.offset() + span.length())
        } else {
            String::new()
        }
    }

    fn json_str(&self, s: &str) -> String {
        let char_count = s.chars().count();
        let truncated = self.opts.max_str_len.is_some_and(|max| char_count > max);
        let chars: Box<dyn Iterator<Item = char>> = if truncated {
            Box::new(s.chars().take(self.opts.max_str_len.unwrap()))
        } else {
            Box::new(s.chars())
        };
        let mut result = String::with_capacity(char_count + 2);
        result.push('"');
        for c in chars {
            match c {
                '"' => result.push_str("\\\""),
                '\\' => result.push_str("\\\\"),
                '\n' => result.push_str("\\n"),
                '\r' => result.push_str("\\r"),
                '\t' => result.push_str("\\t"),
                c if (c as u32) < 0x20 => result.push_str(&format!("\\u{:04x}", c as u32)),
                c => result.push(c),
            }
        }
        result.push('"');
        if truncated {
            result.push_str("...");
        }
        result
    }

    fn fmt_object(&self, obj: &Object) -> String {
        if obj.is_null() {
            return "null".to_owned();
        }
        if let Some(b) = obj.get_bool() {
            return if b { "true".to_owned() } else { "false".to_owned() };
        }
        if let Some(s) = obj.get_str() {
            return self.json_str(s);
        }
        if let Some(i) = obj.get_int() {
            return format!("{i}");
        }
        if let Some(f) = obj.get_float() {
            return format!("{f:?}");
        }
        format!("{obj}")
    }

    // ── ParseResult ───────────────────────────────────────────────────────────

    fn result(&mut self, result: &Result<File, Error>, indent: usize) {
        self.emit(indent, "ParseResult");
        match result {
            Ok(file) => {
                self.emit(indent + 1, "ok: true");
                self.emit(indent + 1, "errors: []");
                self.emit(indent + 1, "tree:");
                self.file(file, indent + 2);
            }
            Err(err) => {
                self.emit(indent + 1, "ok: false");
                self.emit(indent + 1, "errors:");
                let span_str = err.location().map(|s| self.span_str(s)).unwrap_or_default();
                self.emit(indent + 2, format!("ParseError{span_str}"));
                let msg = err.rendered().unwrap_or("parse error");
                self.emit(indent + 3, self.json_str(msg));
                self.emit(indent + 1, "tree: null");
            }
        }
    }

    // ── File ──────────────────────────────────────────────────────────────────

    fn file(&mut self, file: &File, indent: usize) {
        self.emit(indent, "File");
        if file.statements.is_empty() {
            self.emit(indent + 1, "statements: []");
        } else {
            self.emit(indent + 1, "statements:");
            for stmt in &file.statements {
                self.top_level(stmt, indent + 2);
            }
        }
        self.field_expr("expression", &file.expression, indent + 1);
    }

    fn top_level(&mut self, stmt: &TopLevel, indent: usize) {
        let TopLevel::Import(path, binding) = stmt;
        self.emit(indent, "ImportStatement");
        let path_span = self.span_str(path.span());
        self.emit(indent + 1, format!("path: {}{}", self.json_str(path.as_str()), path_span));
        self.field_binding("binding", binding, indent + 1);
    }

    // ── Expressions ───────────────────────────────────────────────────────────

    fn expr(&mut self, expr: &Tagged<Expr>, indent: usize) {
        let span = self.span_str(expr.span());
        self.emit(indent, format!("{}{}", expr_type_name(expr.as_ref()), span));
        self.expr_body(expr.as_ref(), indent + 1);
    }

    fn field_expr(&mut self, name: &str, expr: &Tagged<Expr>, indent: usize) {
        let span = self.span_str(expr.span());
        self.emit(indent, format!("{}: {}{}", name, expr_type_name(expr.as_ref()), span));
        self.expr_body(expr.as_ref(), indent + 1);
    }

    fn expr_body(&mut self, expr: &Expr, indent: usize) {
        match expr {
            Expr::Literal(obj) => {
                self.emit(indent, format!("value: {}", self.fmt_object(obj)));
            }
            Expr::String(elements) => {
                if elements.is_empty() {
                    self.emit(indent, "elements: []");
                } else {
                    self.emit(indent, "elements:");
                    for elem in elements {
                        self.string_element(elem, indent + 1);
                    }
                }
            }
            Expr::Identifier(name) => {
                let span = self.span_str(name.span());
                self.emit(indent, format!("name: {}{}", self.json_str(name.as_str()), span));
            }
            Expr::List(elements) => {
                if elements.is_empty() {
                    self.emit(indent, "elements: []");
                } else {
                    self.emit(indent, "elements:");
                    for elem in elements {
                        self.list_element(elem, indent + 1);
                    }
                }
            }
            Expr::Map(elements) => {
                if elements.is_empty() {
                    self.emit(indent, "elements: []");
                } else {
                    self.emit(indent, "elements:");
                    for elem in elements {
                        self.map_element(elem, indent + 1);
                    }
                }
            }
            Expr::Let { bindings, expression } => {
                if bindings.is_empty() {
                    self.emit(indent, "bindings: []");
                } else {
                    self.emit(indent, "bindings:");
                    for (i, (binding, value)) in bindings.iter().enumerate() {
                        self.emit(indent + 1, format!("[{i}]:"));
                        self.binding(binding, indent + 2);
                        self.expr(value, indent + 2);
                    }
                }
                self.field_expr("expression", expression, indent);
            }
            Expr::Transformed { operand, transform } => {
                self.field_expr("operand", operand, indent);
                self.transform(transform, indent);
            }
            Expr::Function { positional, keywords, expression } => {
                self.field_list_binding("positional", positional, indent);
                match keywords {
                    None => self.emit(indent, "keywords: null"),
                    Some(kw) => self.field_map_binding("keywords", kw, indent),
                }
                self.field_expr("expression", expression, indent);
            }
            Expr::Branch { condition, true_branch, false_branch } => {
                self.field_expr("condition", condition, indent);
                self.field_expr("true_branch", true_branch, indent);
                self.field_expr("false_branch", false_branch, indent);
            }
        }
    }

    // ── String elements ───────────────────────────────────────────────────────

    fn string_element(&mut self, elem: &StringElement, indent: usize) {
        match elem {
            StringElement::Raw(s) => {
                self.emit(indent, "StringRaw");
                self.emit(indent + 1, format!("value: {}", self.json_str(s.as_str())));
            }
            StringElement::Interpolate(expr, fmt) => {
                self.emit(indent, "StringInterpolate");
                self.field_expr("expr", expr, indent + 1);
                match fmt {
                    None => self.emit(indent + 1, "fmt: null"),
                    Some(spec) => {
                        self.emit(indent + 1, "fmt: FormatSpec");
                        self.format_spec(spec, indent + 2);
                    }
                }
            }
        }
    }

    // ── List elements ─────────────────────────────────────────────────────────

    fn list_element(&mut self, elem: &Tagged<ListElement>, indent: usize) {
        let span = self.span_str(elem.span());
        self.emit(indent, format!("{}{}", list_element_type_name(elem.as_ref()), span));
        self.list_element_body(elem.as_ref(), indent + 1);
    }

    fn field_list_element(&mut self, name: &str, elem: &Tagged<ListElement>, indent: usize) {
        let span = self.span_str(elem.span());
        self.emit(indent, format!("{}: {}{}", name, list_element_type_name(elem.as_ref()), span));
        self.list_element_body(elem.as_ref(), indent + 1);
    }

    fn list_element_body(&mut self, elem: &ListElement, indent: usize) {
        match elem {
            ListElement::Singleton(expr) => self.field_expr("expr", expr, indent),
            ListElement::Splat(expr) => self.field_expr("expr", expr, indent),
            ListElement::Loop { binding, iterable, element } => {
                self.field_binding("binding", binding, indent);
                self.field_expr("iterable", iterable, indent);
                self.field_list_element("element", element, indent);
            }
            ListElement::Cond { condition, element } => {
                self.field_expr("condition", condition, indent);
                self.field_list_element("element", element, indent);
            }
        }
    }

    // ── Map elements ──────────────────────────────────────────────────────────

    fn map_element(&mut self, elem: &Tagged<MapElement>, indent: usize) {
        let span = self.span_str(elem.span());
        self.emit(indent, format!("{}{}", map_element_type_name(elem.as_ref()), span));
        self.map_element_body(elem.as_ref(), indent + 1);
    }

    fn field_map_element(&mut self, name: &str, elem: &Tagged<MapElement>, indent: usize) {
        let span = self.span_str(elem.span());
        self.emit(indent, format!("{}: {}{}", name, map_element_type_name(elem.as_ref()), span));
        self.map_element_body(elem.as_ref(), indent + 1);
    }

    fn map_element_body(&mut self, elem: &MapElement, indent: usize) {
        match elem {
            MapElement::Singleton { key, value } => {
                self.field_expr("key", key, indent);
                self.field_expr("value", value, indent);
            }
            MapElement::Splat(expr) => self.field_expr("expr", expr, indent),
            MapElement::Loop { binding, iterable, element } => {
                self.field_binding("binding", binding, indent);
                self.field_expr("iterable", iterable, indent);
                self.field_map_element("element", element, indent);
            }
            MapElement::Cond { condition, element } => {
                self.field_expr("condition", condition, indent);
                self.field_map_element("element", element, indent);
            }
        }
    }

    // ── Arg elements ──────────────────────────────────────────────────────────

    fn arg_element(&mut self, elem: &Tagged<ArgElement>, indent: usize) {
        let span = self.span_str(elem.span());
        self.emit(indent, format!("{}{}", arg_element_type_name(elem.as_ref()), span));
        match elem.as_ref() {
            ArgElement::Singleton(expr) => self.field_expr("expr", expr, indent + 1),
            ArgElement::Keyword(key, expr) => {
                let key_span = self.span_str(key.span());
                self.emit(indent + 1, format!("key: {}{}", self.json_str(key.as_str()), key_span));
                self.field_expr("expr", expr, indent + 1);
            }
            ArgElement::Splat(expr) => self.field_expr("expr", expr, indent + 1),
        }
    }

    // ── Transforms ────────────────────────────────────────────────────────────

    fn transform(&mut self, transform: &Transform, indent: usize) {
        match transform {
            Transform::UnOp(op) => {
                self.emit(indent, "transform: UnOpTransform");
                let span = self.span_str(op.span());
                let name = match op.as_ref() {
                    None => format!("null{span}"),
                    Some(UnOp::ArithmeticalNegate) => format!("ArithmeticalNegate{span}"),
                    Some(UnOp::LogicalNegate) => format!("LogicalNegate{span}"),
                };
                self.emit(indent + 1, format!("op: {name}"));
            }
            Transform::BinOp(op, rhs) => {
                self.emit(indent, "transform: BinOpTransform");
                let op_span = self.span_str(op.span());
                self.emit(indent + 1, format!("op: {}{}", binop_name(op.as_ref()), op_span));
                self.field_expr("operand", rhs, indent + 1);
            }
            Transform::FunCall(args) => {
                self.emit(indent, "transform: FunCallTransform");
                let args_span = self.span_str(args.span());
                if args.as_ref().is_empty() {
                    self.emit(indent + 1, format!("args: []{args_span}"));
                } else {
                    self.emit(indent + 1, format!("args:{args_span}"));
                    for arg in args.as_ref() {
                        self.arg_element(arg, indent + 2);
                    }
                }
            }
        }
    }

    // ── Bindings ──────────────────────────────────────────────────────────────

    fn binding(&mut self, binding: &Tagged<Binding>, indent: usize) {
        let span = self.span_str(binding.span());
        self.emit(indent, format!("{}{}", binding_type_name(binding.as_ref()), span));
        self.binding_body(binding.as_ref(), indent + 1);
    }

    fn field_binding(&mut self, name: &str, binding: &Tagged<Binding>, indent: usize) {
        let span = self.span_str(binding.span());
        self.emit(indent, format!("{}: {}{}", name, binding_type_name(binding.as_ref()), span));
        self.binding_body(binding.as_ref(), indent + 1);
    }

    fn binding_body(&mut self, binding: &Binding, indent: usize) {
        match binding {
            Binding::Identifier(key) => {
                let span = self.span_str(key.span());
                self.emit(indent, format!("name: {}{}", self.json_str(key.as_str()), span));
            }
            Binding::List(lb) => self.field_list_binding("binding", lb, indent),
            Binding::Map(mb) => self.field_map_binding("binding", mb, indent),
        }
    }

    // ── List binding ──────────────────────────────────────────────────────────

    fn field_list_binding(&mut self, name: &str, lb: &Tagged<ListBinding>, indent: usize) {
        let span = self.span_str(lb.span());
        self.emit(indent, format!("{name}: ListBinding{span}"));
        let elems = lb.as_ref().elements();
        if elems.is_empty() {
            self.emit(indent + 1, "elements: []");
        } else {
            self.emit(indent + 1, "elements:");
            for elem in elems {
                self.list_binding_element(elem, indent + 2);
            }
        }
    }

    fn list_binding_element(&mut self, elem: &Tagged<ListBindingElement>, indent: usize) {
        let span = self.span_str(elem.span());
        self.emit(indent, format!("{}{}", list_be_type_name(elem.as_ref()), span));
        match elem.as_ref() {
            ListBindingElement::Binding { binding, default } => {
                self.field_binding("binding", binding, indent + 1);
                match default {
                    None => self.emit(indent + 1, "default: null"),
                    Some(d) => self.field_expr("default", d, indent + 1),
                }
            }
            ListBindingElement::SlurpTo(key) => {
                self.emit(indent + 1, format!("name: {}", self.json_str(key.as_str())));
            }
            ListBindingElement::Slurp => {}
        }
    }

    // ── Map binding ───────────────────────────────────────────────────────────

    fn field_map_binding(&mut self, name: &str, mb: &Tagged<MapBinding>, indent: usize) {
        let span = self.span_str(mb.span());
        self.emit(indent, format!("{name}: MapBinding{span}"));
        let elems = mb.as_ref().elements();
        if elems.is_empty() {
            self.emit(indent + 1, "elements: []");
        } else {
            self.emit(indent + 1, "elements:");
            for elem in elems {
                self.map_binding_element(elem, indent + 2);
            }
        }
    }

    fn map_binding_element(&mut self, elem: &Tagged<MapBindingElement>, indent: usize) {
        let span = self.span_str(elem.span());
        self.emit(indent, format!("{}{}", map_be_type_name(elem.as_ref()), span));
        match elem.as_ref() {
            MapBindingElement::Binding { key, binding, default } => {
                let key_span = self.span_str(key.span());
                self.emit(indent + 1, format!("key: {}{}", self.json_str(key.as_str()), key_span));
                self.field_binding("binding", binding, indent + 1);
                match default {
                    None => self.emit(indent + 1, "default: null"),
                    Some(d) => self.field_expr("default", d, indent + 1),
                }
            }
            MapBindingElement::SlurpTo(key) => {
                self.emit(indent + 1, format!("name: {}", self.json_str(key.as_str())));
            }
        }
    }

    // ── FormatSpec ────────────────────────────────────────────────────────────

    fn format_spec(&mut self, spec: &FormatSpec, indent: usize) {
        self.emit(indent, format!("fill: {}", self.json_str(&spec.fill.to_string())));
        match spec.align {
            None => self.emit(indent, "align: null"),
            Some(ref a) => self.emit(indent, format!("align: {}", align_name(a))),
        }
        match spec.sign {
            None => self.emit(indent, "sign: null"),
            Some(ref s) => self.emit(indent, format!("sign: {}", sign_name(s))),
        }
        self.emit(indent, format!("alternate: {}", if spec.alternate { "true" } else { "false" }));
        match spec.width {
            None => self.emit(indent, "width: null"),
            Some(w) => self.emit(indent, format!("width: {w}")),
        }
        match spec.grouping {
            None => self.emit(indent, "grouping: null"),
            Some(ref g) => self.emit(indent, format!("grouping: {}", grouping_name(g))),
        }
        match spec.precision {
            None => self.emit(indent, "precision: null"),
            Some(p) => self.emit(indent, format!("precision: {p}")),
        }
        match spec.fmt_type {
            None => self.emit(indent, "fmt_type: null"),
            Some(ref t) => self.emit(indent, format!("fmt_type: {}", fmt_type_name(t))),
        }
    }
}

// ── Name helpers ──────────────────────────────────────────────────────────────

fn expr_type_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Literal(_) => "LiteralExpr",
        Expr::String(_) => "StringExpr",
        Expr::Identifier(_) => "IdentifierExpr",
        Expr::List(_) => "ListExpr",
        Expr::Map(_) => "MapExpr",
        Expr::Let { .. } => "LetExpr",
        Expr::Transformed { .. } => "TransformedExpr",
        Expr::Function { .. } => "FunctionExpr",
        Expr::Branch { .. } => "BranchExpr",
    }
}

fn binding_type_name(b: &Binding) -> &'static str {
    match b {
        Binding::Identifier(_) => "IdentifierBinding",
        Binding::List(_) => "ListPatternBinding",
        Binding::Map(_) => "MapPatternBinding",
    }
}

fn list_element_type_name(e: &ListElement) -> &'static str {
    match e {
        ListElement::Singleton(_) => "ListSingleton",
        ListElement::Splat(_) => "ListSplat",
        ListElement::Loop { .. } => "ListLoop",
        ListElement::Cond { .. } => "ListCond",
    }
}

fn map_element_type_name(e: &MapElement) -> &'static str {
    match e {
        MapElement::Singleton { .. } => "MapSingleton",
        MapElement::Splat(_) => "MapSplat",
        MapElement::Loop { .. } => "MapLoop",
        MapElement::Cond { .. } => "MapCond",
    }
}

fn arg_element_type_name(e: &ArgElement) -> &'static str {
    match e {
        ArgElement::Singleton(_) => "ArgSingleton",
        ArgElement::Keyword(_, _) => "ArgKeyword",
        ArgElement::Splat(_) => "ArgSplat",
    }
}

fn list_be_type_name(e: &ListBindingElement) -> &'static str {
    match e {
        ListBindingElement::Binding { .. } => "ListBindingSingleton",
        ListBindingElement::SlurpTo(_) => "ListBindingSlurpTo",
        ListBindingElement::Slurp => "ListBindingSlurp",
    }
}

fn map_be_type_name(e: &MapBindingElement) -> &'static str {
    match e {
        MapBindingElement::Binding { .. } => "MapBindingSingleton",
        MapBindingElement::SlurpTo(_) => "MapBindingSlurpTo",
    }
}

fn binop_name(op: &BinOp) -> &'static str {
    match op {
        BinOp::Eager(EagerOp::Index) => "Index",
        BinOp::Eager(EagerOp::Power) => "Power",
        BinOp::Eager(EagerOp::Multiply) => "Multiply",
        BinOp::Eager(EagerOp::IntegerDivide) => "IntegerDivide",
        BinOp::Eager(EagerOp::Divide) => "Divide",
        BinOp::Eager(EagerOp::Add) => "Add",
        BinOp::Eager(EagerOp::Subtract) => "Subtract",
        BinOp::Eager(EagerOp::Less) => "Less",
        BinOp::Eager(EagerOp::Greater) => "Greater",
        BinOp::Eager(EagerOp::LessEqual) => "LessEqual",
        BinOp::Eager(EagerOp::GreaterEqual) => "GreaterEqual",
        BinOp::Eager(EagerOp::Equal) => "Equal",
        BinOp::Eager(EagerOp::NotEqual) => "NotEqual",
        BinOp::Eager(EagerOp::Contains) => "Contains",
        BinOp::Logic(LogicOp::And) => "And",
        BinOp::Logic(LogicOp::Or) => "Or",
    }
}

fn align_name(a: &AlignSpec) -> &'static str {
    match a {
        AlignSpec::AfterSign => "AfterSign",
        AlignSpec::String(StringAlignSpec::Left) => "Left",
        AlignSpec::String(StringAlignSpec::Right) => "Right",
        AlignSpec::String(StringAlignSpec::Center) => "Center",
    }
}

fn sign_name(s: &SignSpec) -> &'static str {
    match s {
        SignSpec::Plus => "Plus",
        SignSpec::Minus => "Minus",
        SignSpec::Space => "Space",
    }
}

fn grouping_name(g: &GroupingSpec) -> &'static str {
    match g {
        GroupingSpec::Comma => "Comma",
        GroupingSpec::Underscore => "Underscore",
    }
}

fn fmt_type_name(t: &FormatType) -> &'static str {
    match t {
        FormatType::String => "String",
        FormatType::Integer(IntegerFormatType::Binary) => "Binary",
        FormatType::Integer(IntegerFormatType::Character) => "Character",
        FormatType::Integer(IntegerFormatType::Decimal) => "Decimal",
        FormatType::Integer(IntegerFormatType::Octal) => "Octal",
        FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower)) => "HexLower",
        FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Upper)) => "HexUpper",
        FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Lower)) => "SciLower",
        FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Upper)) => "SciUpper",
        FormatType::Float(FloatFormatType::Fixed) => "Fixed",
        FormatType::Float(FloatFormatType::General) => "General",
        FormatType::Float(FloatFormatType::Percentage) => "Percentage",
    }
}
