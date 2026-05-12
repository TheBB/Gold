from __future__ import annotations

import math
from abc import ABC, abstractmethod
from pathlib import Path  # noqa: TC003
from typing import Any, TypeGuard

from .ast import (
    AlignSpec,
    ArgKeyword,
    ArgSingleton,
    ArgSplat,
    BinOpTransform,
    BranchExpr,
    EagerOp,
    File,
    FormatSpec,
    FormatTypeSpec,
    FunCallTransform,
    FunctionExpr,
    GoldBuiltin,
    GoldFunction,
    GoldValue,
    GroupingSpec,
    IdentifierBinding,
    IdentifierExpr,
    ImportStatement,
    LetExpr,
    ListBinding,
    ListBindingSingleton,
    ListBindingSlurp,
    ListBindingSlurpTo,
    ListCond,
    ListExpr,
    ListLoop,
    ListPatternBinding,
    ListSingleton,
    ListSplat,
    LiteralExpr,
    LogicOp,
    MapBinding,
    MapBindingSingleton,
    MapBindingSlurpTo,
    MapCond,
    MapExpr,
    MapLoop,
    MapPatternBinding,
    MapSingleton,
    MapSplat,
    MissingBinding,
    MissingExpr,
    SignSpec,
    StringExpr,
    StringInterpolate,
    StringRaw,
    TransformedExpr,
    UnOp,
    UnOpTransform,
)
from .span import Tagged  # noqa: TC001

# ── Errors ────────────────────────────────────────────────────────────────────


class EvalError(Exception):
    pass


# ── Truthiness ────────────────────────────────────────────────────────────────


def _truthy(v: GoldValue) -> bool:
    if v is None or v is False:
        return False
    if isinstance(v, bool):
        return True
    if isinstance(v, int):
        return v != 0
    if isinstance(v, float):
        return v != 0.0
    return True


# ── String conversion ─────────────────────────────────────────────────────────


def _gold_str(v: GoldValue) -> str:
    if v is None:
        return "null"
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, float):
        return str(v)
    if isinstance(v, str):
        return v
    if isinstance(v, list):
        return "[" + ", ".join(_gold_str(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{" + ", ".join(f"{k}: {_gold_str(val)}" for k, val in v.items()) + "}"
    raise EvalError(f"cannot convert {type(v).__name__!r} to string")


# ── Format spec application ───────────────────────────────────────────────────


def _format_value(v: GoldValue, fmt: FormatSpec) -> str:
    spec = ""
    if fmt.align is not None:
        spec += fmt.fill
        match fmt.align:
            case AlignSpec.Left:
                spec += "<"
            case AlignSpec.Right:
                spec += ">"
            case AlignSpec.Center:
                spec += "^"
            case AlignSpec.AfterSign:
                spec += "="
    if fmt.sign is not None:
        match fmt.sign:
            case SignSpec.Plus:
                spec += "+"
            case SignSpec.Minus:
                spec += "-"
            case SignSpec.Space:
                spec += " "
    if fmt.alternate:
        spec += "#"
    if fmt.width is not None:
        spec += str(fmt.width)
    if fmt.grouping is not None:
        match fmt.grouping:
            case GroupingSpec.Comma:
                spec += ","
            case GroupingSpec.Underscore:
                spec += "_"
    if fmt.precision is not None:
        spec += f".{fmt.precision}"
    if fmt.fmt_type is not None:
        match fmt.fmt_type:
            case FormatTypeSpec.String:
                spec += "s"
            case FormatTypeSpec.Binary:
                spec += "b"
            case FormatTypeSpec.Character:
                spec += "c"
            case FormatTypeSpec.Decimal:
                spec += "d"
            case FormatTypeSpec.Octal:
                spec += "o"
            case FormatTypeSpec.HexLower:
                spec += "x"
            case FormatTypeSpec.HexUpper:
                spec += "X"
            case FormatTypeSpec.SciLower:
                spec += "e"
            case FormatTypeSpec.SciUpper:
                spec += "E"
            case FormatTypeSpec.Fixed:
                spec += "f"
            case FormatTypeSpec.General:
                spec += "g"
            case FormatTypeSpec.Percentage:
                spec += "%"
    try:
        return format(v, spec)
    except (TypeError, ValueError) as e:
        raise EvalError(f"format error: {e}") from e


# ── Namespace ─────────────────────────────────────────────────────────────────


class Namespace:
    """A lexical scope: a dict with an optional parent chain."""

    def __init__(self, parent: Namespace | None = None) -> None:
        self._parent = parent
        self._bindings: dict[str, GoldValue] = {}

    def lookup(self, name: str) -> GoldValue:
        ns: Namespace | None = self
        while ns is not None:
            if name in ns._bindings:
                return ns._bindings[name]
            ns = ns._parent
        raise EvalError(f"undefined name: {name!r}")

    def bind(self, name: str, value: GoldValue) -> None:
        self._bindings[name] = value

    def child(self) -> Namespace:
        return Namespace(parent=self)


# ── Import resolver ───────────────────────────────────────────────────────────


class AbstractImportResolver(ABC):
    @abstractmethod
    def resolve(self, path: str) -> GoldValue: ...


class PathImportResolver(AbstractImportResolver):
    def __init__(self, root: Path) -> None:
        self._root = root

    def resolve(self, path: str) -> GoldValue:
        from .parser import parse

        full_path = self._root / path
        source = full_path.read_text(encoding="utf-8")
        result = parse(source)
        if not result.ok or result.tree is None:
            raise EvalError(f"import {path!r}: parse failed")
        child_resolver = PathImportResolver(full_path.parent)
        return evaluate(result.tree, child_resolver)


# ── Binding resolution ────────────────────────────────────────────────────────


def _resolve_binding(binding_tagged: Tagged[Any], value: GoldValue, ns: Namespace) -> None:
    b = binding_tagged.contents
    if isinstance(b, IdentifierBinding):
        ns.bind(b.name.contents, value)
    elif isinstance(b, ListPatternBinding):
        _resolve_list_binding(b.binding.contents, value, ns)
    elif isinstance(b, MapPatternBinding):
        _resolve_map_binding(b.binding.contents, value, ns)
    elif isinstance(b, MissingBinding):
        pass
    else:
        raise EvalError(f"unknown binding type: {type(b).__name__!r}")


def _resolve_list_binding(lb: ListBinding, value: GoldValue, ns: Namespace) -> None:
    if not isinstance(value, list):
        raise EvalError(f"cannot unpack {type(value).__name__!r} as list")

    elements = lb.elements
    slurp_pos: int | None = next(
        (i for i, e in enumerate(elements) if isinstance(e.contents, (ListBindingSlurpTo, ListBindingSlurp))),
        None,
    )
    pre = elements[: slurp_pos if slurp_pos is not None else len(elements)]
    post = elements[slurp_pos + 1 :] if slurp_pos is not None else []

    required = sum(
        1 for e in pre if isinstance(e.contents, ListBindingSingleton) and e.contents.default is None
    ) + len(post)
    if len(value) < required:
        raise EvalError(f"expected at least {required} list elements, got {len(value)}")

    idx = 0
    for elem_tagged in pre:
        elem = elem_tagged.contents
        assert isinstance(elem, ListBindingSingleton)
        if idx < len(value):
            _resolve_binding(elem.binding, value[idx], ns)
            idx += 1
        elif elem.default is not None:
            _resolve_binding(elem.binding, _eval_expr(elem.default, ns), ns)
        else:
            raise EvalError("missing required positional argument")

    if slurp_pos is not None:
        slurp = elements[slurp_pos].contents
        post_len = len(post)
        slurp_items = value[idx : len(value) - post_len] if post_len else value[idx:]
        if isinstance(slurp, ListBindingSlurpTo):
            ns.bind(slurp.name, list(slurp_items))

    for i, elem_tagged in enumerate(post):
        elem = elem_tagged.contents
        assert isinstance(elem, ListBindingSingleton)
        _resolve_binding(elem.binding, value[len(value) - len(post) + i], ns)


def _resolve_map_binding(mb: MapBinding, value: GoldValue, ns: Namespace) -> None:
    if not isinstance(value, dict):
        raise EvalError(f"cannot unpack {type(value).__name__!r} as map")

    consumed: set[str] = set()
    for elem_tagged in mb.elements:
        elem = elem_tagged.contents
        if isinstance(elem, MapBindingSingleton):
            k = elem.key.contents
            if k in value:
                _resolve_binding(elem.binding, value[k], ns)
                consumed.add(k)
            elif elem.default is not None:
                _resolve_binding(elem.binding, _eval_expr(elem.default, ns), ns)
            else:
                raise EvalError(f"missing required key {k!r}")
        elif isinstance(elem, MapBindingSlurpTo):
            rest: dict[str, GoldValue] = {k: v for k, v in value.items() if k not in consumed}
            ns.bind(elem.name, rest)


# ── Type helpers ──────────────────────────────────────────────────────────────


def _is_int(v: GoldValue) -> TypeGuard[int]:
    return isinstance(v, int) and not isinstance(v, bool)


def _is_float(v: GoldValue) -> TypeGuard[float]:
    return isinstance(v, float)


def _is_numeric(v: GoldValue) -> TypeGuard[int | float]:
    return _is_int(v) or _is_float(v)


# ── Eager binary operators ────────────────────────────────────────────────────


def _gold_eq(a: GoldValue, b: GoldValue) -> bool:
    if isinstance(a, bool) or isinstance(b, bool):
        return type(a) is type(b) and a == b
    if _is_int(a) and _is_int(b):
        return a == b
    if _is_numeric(a) and _is_numeric(b):
        return float(a) == float(b)
    return type(a) is type(b) and a == b


def _compare(a: GoldValue, b: GoldValue) -> int:
    if _is_numeric(a) and _is_numeric(b):
        fa, fb = float(a), float(b)
        return (fa > fb) - (fa < fb)
    if isinstance(a, str) and isinstance(b, str):
        return (a > b) - (a < b)
    raise EvalError(f"cannot compare {type(a).__name__!r} and {type(b).__name__!r}")


def _eval_eager_op(op: EagerOp, lhs: GoldValue, rhs: GoldValue) -> GoldValue:
    match op:
        case EagerOp.Add:
            if _is_int(lhs) and _is_int(rhs):
                return lhs + rhs
            if _is_numeric(lhs) and _is_numeric(rhs):
                return float(lhs) + float(rhs)
            if isinstance(lhs, str) and isinstance(rhs, str):
                return lhs + rhs
            if isinstance(lhs, list) and isinstance(rhs, list):
                return lhs + rhs
            raise EvalError(f"cannot add {type(lhs).__name__!r} and {type(rhs).__name__!r}")

        case EagerOp.Subtract:
            if _is_int(lhs) and _is_int(rhs):
                return lhs - rhs
            if _is_numeric(lhs) and _is_numeric(rhs):
                return float(lhs) - float(rhs)
            raise EvalError(f"cannot subtract {type(lhs).__name__!r} and {type(rhs).__name__!r}")

        case EagerOp.Multiply:
            if _is_int(lhs) and _is_int(rhs):
                return lhs * rhs
            if _is_numeric(lhs) and _is_numeric(rhs):
                return float(lhs) * float(rhs)
            raise EvalError(f"cannot multiply {type(lhs).__name__!r} and {type(rhs).__name__!r}")

        case EagerOp.Divide:
            if not _is_numeric(lhs) or not _is_numeric(rhs):
                raise EvalError("division requires numbers")
            if rhs == 0:
                raise EvalError("division by zero")
            return float(lhs) / float(rhs)

        case EagerOp.IntegerDivide:
            if not _is_int(lhs) or not _is_int(rhs):
                raise EvalError("integer division requires integers")
            if rhs == 0:
                raise EvalError("integer division by zero")
            return lhs // rhs

        case EagerOp.Power:
            if not _is_numeric(lhs) or not _is_numeric(rhs):
                raise EvalError("power requires numbers")
            if _is_int(lhs) and _is_int(rhs) and rhs >= 0:
                return int(lhs) ** int(rhs)
            return float(lhs) ** float(rhs)

        case EagerOp.Less:
            return _compare(lhs, rhs) < 0
        case EagerOp.Greater:
            return _compare(lhs, rhs) > 0
        case EagerOp.LessEqual:
            return _compare(lhs, rhs) <= 0
        case EagerOp.GreaterEqual:
            return _compare(lhs, rhs) >= 0
        case EagerOp.Equal:
            return _gold_eq(lhs, rhs)
        case EagerOp.NotEqual:
            return not _gold_eq(lhs, rhs)

        case EagerOp.Index:
            if isinstance(lhs, list) and _is_int(rhs):
                try:
                    return lhs[int(rhs)]
                except IndexError:
                    raise EvalError(f"list index {rhs} out of range") from None
            if isinstance(lhs, dict) and isinstance(rhs, str):
                if rhs not in lhs:
                    raise EvalError(f"key {rhs!r} not found in map")
                return lhs[rhs]
            raise EvalError(f"cannot index {type(lhs).__name__!r} with {type(rhs).__name__!r}")

        case EagerOp.Contains:
            # Gold syntax: container has element  (lhs=container, rhs=element)
            if isinstance(lhs, list):
                return any(_gold_eq(rhs, x) for x in lhs)
            if isinstance(lhs, dict) and isinstance(rhs, str):
                return rhs in lhs
            if isinstance(lhs, str) and isinstance(rhs, str):
                return rhs in lhs
            raise EvalError(f"cannot check containment in {type(lhs).__name__!r}")

    raise EvalError(f"unknown op: {op!r}")


# ── Built-in functions ────────────────────────────────────────────────────────

_Builtin = Any  # Callable[[list[EvalValue], dict[str, EvalValue]], EvalValue]


def _builtin_len(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("len() takes exactly 1 positional argument")
    x = args[0]
    if isinstance(x, (str, list, dict)):
        return len(x)
    raise EvalError("len() requires str, list, or map")


def _builtin_range(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if kwargs:
        raise EvalError("range() takes no keyword arguments")
    if len(args) == 1 and _is_int(args[0]):
        return list(range(int(args[0])))
    if len(args) == 2 and _is_int(args[0]) and _is_int(args[1]):
        return list(range(int(args[0]), int(args[1])))
    raise EvalError("range() takes 1 or 2 integer arguments")


def _builtin_int(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("int() takes exactly 1 argument")
    x = args[0]
    if _is_int(x):
        return x
    if _is_float(x):
        return int(round(float(x)))
    if isinstance(x, bool):
        return 1 if x else 0
    if isinstance(x, str):
        try:
            return int(x)
        except ValueError:
            raise EvalError(f"cannot convert {x!r} to integer") from None
    raise EvalError(f"cannot convert {type(x).__name__!r} to integer")


def _builtin_float(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("float() takes exactly 1 argument")
    x = args[0]
    if _is_float(x):
        return x
    if _is_int(x):
        return float(int(x))
    if isinstance(x, bool):
        return 1.0 if x else 0.0
    if isinstance(x, str):
        try:
            return float(x)
        except ValueError:
            raise EvalError(f"cannot convert {x!r} to float") from None
    raise EvalError(f"cannot convert {type(x).__name__!r} to float")


def _builtin_bool(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("bool() takes exactly 1 argument")
    return _truthy(args[0])


def _builtin_str(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("str() takes exactly 1 argument")
    return _gold_str(args[0])


def _builtin_map_fn(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2 or kwargs:
        raise EvalError("map() takes exactly 2 positional arguments")
    f, xs = args[0], args[1]
    if not isinstance(f, (GoldFunction, GoldBuiltin)):
        raise EvalError("map() first argument must be a function")
    if not isinstance(xs, list):
        raise EvalError("map() second argument must be a list")
    return [_call(f, [x], {}) for x in xs]


def _builtin_filter_fn(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2 or kwargs:
        raise EvalError("filter() takes exactly 2 positional arguments")
    f, xs = args[0], args[1]
    if not isinstance(f, (GoldFunction, GoldBuiltin)):
        raise EvalError("filter() first argument must be a function")
    if not isinstance(xs, list):
        raise EvalError("filter() second argument must be a list")
    return [x for x in xs if _truthy(_call(f, [x], {}))]


def _builtin_items(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("items() takes exactly 1 argument")
    x = args[0]
    if not isinstance(x, dict):
        raise EvalError("items() argument must be a map")
    return [[k, v] for k, v in x.items()]


def _builtin_exp(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise EvalError("exp() takes exactly 1 positional argument")
    x = args[0]
    if not _is_numeric(x):
        raise EvalError("exp() argument must be a number")
    xf = float(x)
    if "base" in kwargs:
        base = kwargs["base"]
        if not _is_numeric(base):
            raise EvalError("exp() base must be a number")
        return float(base) ** xf
    return math.exp(xf)


def _builtin_log(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise EvalError("log() takes exactly 1 positional argument")
    x = args[0]
    if not _is_numeric(x):
        raise EvalError("log() argument must be a number")
    xf = float(x)
    if "base" in kwargs:
        base = kwargs["base"]
        if not _is_numeric(base):
            raise EvalError("log() base must be a number")
        return math.log(xf, float(base))
    return math.log(xf)


def _builtin_ord(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("ord() takes exactly 1 argument")
    x = args[0]
    if not isinstance(x, str) or len(x) != 1:
        raise EvalError("ord() argument must be a single-character string")
    return ord(x)


def _builtin_chr(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1 or kwargs:
        raise EvalError("chr() takes exactly 1 argument")
    x = args[0]
    if not _is_int(x):
        raise EvalError("chr() argument must be an integer")
    try:
        return chr(int(x))
    except (ValueError, OverflowError) as e:
        raise EvalError(f"invalid codepoint: {x}") from e


def _builtin_startswith(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2 or kwargs:
        raise EvalError("startswith() takes exactly 2 arguments")
    x, y = args
    if not isinstance(x, str) or not isinstance(y, str):
        raise EvalError("startswith() arguments must be strings")
    return x.startswith(y)


def _builtin_endswith(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2 or kwargs:
        raise EvalError("endswith() takes exactly 2 arguments")
    x, y = args
    if not isinstance(x, str) or not isinstance(y, str):
        raise EvalError("endswith() arguments must be strings")
    return x.endswith(y)


def _builtin_isint(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and _is_int(args[0])


def _builtin_isstr(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and isinstance(args[0], str)


def _builtin_isnull(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and args[0] is None


def _builtin_isbool(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and isinstance(args[0], bool)


def _builtin_isfloat(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and _is_float(args[0])


def _builtin_isnumber(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and _is_numeric(args[0])


def _builtin_isobject(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and isinstance(args[0], dict)


def _builtin_islist(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and isinstance(args[0], list)


def _builtin_isfunc(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    return len(args) == 1 and isinstance(args[0], (GoldFunction, GoldBuiltin))


_BUILTIN_TABLE: dict[str, _Builtin] = {
    "len": _builtin_len,
    "range": _builtin_range,
    "int": _builtin_int,
    "float": _builtin_float,
    "bool": _builtin_bool,
    "str": _builtin_str,
    "map": _builtin_map_fn,
    "filter": _builtin_filter_fn,
    "items": _builtin_items,
    "exp": _builtin_exp,
    "log": _builtin_log,
    "ord": _builtin_ord,
    "chr": _builtin_chr,
    "startswith": _builtin_startswith,
    "endswith": _builtin_endswith,
    "isint": _builtin_isint,
    "isstr": _builtin_isstr,
    "isnull": _builtin_isnull,
    "isbool": _builtin_isbool,
    "isfloat": _builtin_isfloat,
    "isnumber": _builtin_isnumber,
    "isobject": _builtin_isobject,
    "islist": _builtin_islist,
    "isfunc": _builtin_isfunc,
}


# ── Function calling ──────────────────────────────────────────────────────────


def _call(func: GoldValue, args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if isinstance(func, GoldBuiltin):
        return _BUILTIN_TABLE[func.name](args, kwargs)
    if isinstance(func, GoldFunction):
        call_ns = func.captured.child()
        _resolve_list_binding(func.positional, args, call_ns)
        if func.keywords is not None:
            _resolve_map_binding(func.keywords, kwargs, call_ns)
        return _eval_expr(func.body, call_ns)
    raise EvalError(f"cannot call {type(func).__name__!r}")


def _eval_args(arg_elems: list[Tagged[Any]], ns: Namespace) -> tuple[list[GoldValue], dict[str, GoldValue]]:
    pos: list[GoldValue] = []
    kw: dict[str, GoldValue] = {}
    for arg_tagged in arg_elems:
        a = arg_tagged.contents
        if isinstance(a, ArgSingleton):
            pos.append(_eval_expr(a.expr, ns))
        elif isinstance(a, ArgKeyword):
            kw[a.key.contents] = _eval_expr(a.expr, ns)
        elif isinstance(a, ArgSplat):
            val = _eval_expr(a.expr, ns)
            if isinstance(val, list):
                pos.extend(val)
            elif isinstance(val, dict):
                kw.update(val)
            else:
                raise EvalError("splat argument must be list or map")
    return pos, kw


# ── List / map element helpers ────────────────────────────────────────────────


def _eval_list_element(elem_tagged: Tagged[Any], ns: Namespace) -> list[GoldValue]:
    e = elem_tagged.contents
    if isinstance(e, ListSingleton):
        return [_eval_expr(e.expr, ns)]
    if isinstance(e, ListSplat):
        val = _eval_expr(e.expr, ns)
        if not isinstance(val, list):
            raise EvalError("list splat requires a list")
        return val
    if isinstance(e, ListLoop):
        items = _eval_expr(e.iterable, ns)
        if not isinstance(items, list):
            raise EvalError("for-loop iterable must be a list")
        result: list[GoldValue] = []
        for item in items:
            loop_ns = ns.child()
            _resolve_binding(e.binding, item, loop_ns)
            result.extend(_eval_list_element(e.element, loop_ns))
        return result
    if isinstance(e, ListCond):
        if _truthy(_eval_expr(e.condition, ns)):
            return _eval_list_element(e.element, ns)
        return []
    raise EvalError(f"unexpected list element type: {type(e).__name__!r}")


def _eval_map_element(elem_tagged: Tagged[Any], ns: Namespace) -> dict[str, GoldValue]:
    e = elem_tagged.contents
    if isinstance(e, MapSingleton):
        k = _eval_expr(e.key, ns)
        if not isinstance(k, str):
            raise EvalError("map key must be a string")
        return {k: _eval_expr(e.value, ns)}
    if isinstance(e, MapSplat):
        val = _eval_expr(e.expr, ns)
        if not isinstance(val, dict):
            raise EvalError("map splat requires a map")
        return dict(val)
    if isinstance(e, MapLoop):
        items = _eval_expr(e.iterable, ns)
        if not isinstance(items, list):
            raise EvalError("for-loop iterable must be a list")
        result: dict[str, GoldValue] = {}
        for item in items:
            loop_ns = ns.child()
            _resolve_binding(e.binding, item, loop_ns)
            result.update(_eval_map_element(e.element, loop_ns))
        return result
    if isinstance(e, MapCond):
        if _truthy(_eval_expr(e.condition, ns)):
            return _eval_map_element(e.element, ns)
        return {}
    raise EvalError(f"unexpected map element type: {type(e).__name__!r}")


# ── Expression evaluation ─────────────────────────────────────────────────────


def _eval_expr(expr: Tagged[Any], ns: Namespace) -> GoldValue:
    node = expr.contents

    if isinstance(node, LiteralExpr):
        return node.value

    if isinstance(node, StringExpr):
        parts: list[str] = []
        for elem in node.elements:
            if isinstance(elem, StringRaw):
                parts.append(elem.value)
            elif isinstance(elem, StringInterpolate):
                v = _eval_expr(elem.expr, ns)
                parts.append(_format_value(v, elem.fmt) if elem.fmt is not None else _gold_str(v))
        return "".join(parts)

    if isinstance(node, IdentifierExpr):
        return ns.lookup(node.name.contents)

    if isinstance(node, ListExpr):
        result_list: list[GoldValue] = []
        for elem_tagged in node.elements:
            result_list.extend(_eval_list_element(elem_tagged, ns))
        return result_list

    if isinstance(node, MapExpr):
        result_map: dict[str, GoldValue] = {}
        for elem_tagged in node.elements:
            result_map.update(_eval_map_element(elem_tagged, ns))
        return result_map

    if isinstance(node, LetExpr):
        let_ns = ns.child()
        for binding, val_expr in node.bindings:
            _resolve_binding(binding, _eval_expr(val_expr, let_ns), let_ns)
        return _eval_expr(node.expression, let_ns)

    if isinstance(node, BranchExpr):
        if _truthy(_eval_expr(node.condition, ns)):
            return _eval_expr(node.true_branch, ns)
        return _eval_expr(node.false_branch, ns)

    if isinstance(node, FunctionExpr):
        return GoldFunction(
            positional=node.positional.contents,
            keywords=node.keywords.contents if node.keywords is not None else None,
            body=node.expression,
            captured=ns,
        )

    if isinstance(node, TransformedExpr):
        t = node.transform

        if isinstance(t, UnOpTransform):
            if t.op.contents is None:
                return _eval_expr(node.operand, ns)
            val = _eval_expr(node.operand, ns)
            match t.op.contents:
                case UnOp.ArithmeticalNegate:
                    if _is_int(val):
                        return -(val)
                    if _is_float(val):
                        return -(val)
                    raise EvalError(f"cannot negate {type(val).__name__!r}")
                case UnOp.LogicalNegate:
                    return not _truthy(val)

        if isinstance(t, BinOpTransform):
            op = t.op.contents
            if isinstance(op, LogicOp):
                lhs = _eval_expr(node.operand, ns)
                if op == LogicOp.And:
                    return lhs if not _truthy(lhs) else _eval_expr(t.operand, ns)
                return lhs if _truthy(lhs) else _eval_expr(t.operand, ns)
            lhs = _eval_expr(node.operand, ns)
            rhs = _eval_expr(t.operand, ns)
            return _eval_eager_op(op, lhs, rhs)

        if isinstance(t, FunCallTransform):
            func = _eval_expr(node.operand, ns)
            pos_args, kw_args = _eval_args(t.args.contents, ns)
            return _call(func, pos_args, kw_args)

    if isinstance(node, MissingExpr):
        raise EvalError("missing expression (parse error in source)")

    raise EvalError(f"unexpected expression node: {type(node).__name__!r}")


# ── Root namespace ────────────────────────────────────────────────────────────


def _make_builtins_namespace() -> Namespace:
    ns = Namespace()
    for name in _BUILTIN_TABLE:
        ns.bind(name, GoldBuiltin(name=name))
    return ns


_BUILTINS_NS: Namespace = _make_builtins_namespace()


# ── Public API ────────────────────────────────────────────────────────────────


def evaluate(file: File, resolver: AbstractImportResolver | None = None) -> GoldValue:
    """Evaluate a parsed Gold ``File`` AST and return the result value."""
    ns = _BUILTINS_NS.child()

    for stmt in file.statements:
        if isinstance(stmt, ImportStatement):
            if resolver is None:
                raise EvalError(f"import {stmt.path.contents!r}: no resolver provided")
            value = resolver.resolve(stmt.path.contents)
            _resolve_binding(stmt.binding, value, ns)

    return _eval_expr(file.expression, ns)


def evaluate_source(source: str, resolver: AbstractImportResolver | None = None) -> GoldValue:
    """Parse ``source`` and evaluate it, returning the result value."""
    from .parser import parse

    result = parse(source)
    if not result.ok or result.tree is None:
        errors = "; ".join(e.message for e in result.errors)
        raise EvalError(f"parse failed: {errors}")
    return evaluate(result.tree, resolver)
