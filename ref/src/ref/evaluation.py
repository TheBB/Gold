from __future__ import annotations

import math
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, TypeGuard, Unpack

from .ast import (
    AlignSpec,
    ArgKeyword,
    ArgSingleton,
    ArgSplat,
    Binding,
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
from .error import (
    Action,
    BindingType,
    Error,
    ObjectType,
    ReasonExternal,
    ReasonUnassigned,
    ReasonUnbound,
    TypeMismatchArgCount,
    TypeMismatchBinOp,
    TypeMismatchCall,
    TypeMismatchExpectedKwarg,
    TypeMismatchExpectedPosArg,
    TypeMismatchInterpolate,
    TypeMismatchIterate,
    TypeMismatchMapKey,
    TypeMismatchSplatArg,
    TypeMismatchSplatList,
    TypeMismatchSplatMap,
    TypeMismatchUnOp,
    UnpackKeyMissing,
    UnpackListTooLong,
    UnpackListTooShort,
    UnpackTypeMismatch,
    ValueConvert,
    ValueOutOfRange,
    ValueTooLong,
)
from .parser import parse
from .pprint import PrintOpts, pprint_eval_result


if TYPE_CHECKING:
    from pathlib import Path

    from .span import Tagged


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
    raise ReasonExternal(f"cannot convert {type(v).__name__!r} to string").err()


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
        raise ReasonExternal(str(e)).err() from e


# ── Namespace ─────────────────────────────────────────────────────────────────


class Namespace:
    """A lexical scope: a dict with an optional parent chain."""

    _parent: Namespace | None
    _bindings: dict[str, GoldValue]

    def __init__(self, parent: Namespace | None = None) -> None:
        self._parent = parent
        self._bindings = {}

    def lookup(self, name: str) -> GoldValue:
        ns: Namespace | None = self
        while ns is not None:
            if name in ns._bindings:
                return ns._bindings[name]
            ns = ns._parent
        raise ReasonUnbound(name).err()

    def bind(self, name: str, value: GoldValue) -> None:
        self._bindings[name] = value

    def child(self) -> Namespace:
        return Namespace(parent=self)


# ── Import resolver ───────────────────────────────────────────────────────────


class AbstractImportResolver(ABC):
    @abstractmethod
    def resolve(self, path: str) -> GoldValue: ...


class PathImportResolver(AbstractImportResolver):
    _root: Path

    def __init__(self, root: Path) -> None:
        self._root = root

    def resolve(self, path: str) -> GoldValue:
        full_path = self._root / path
        source = full_path.read_text(encoding="utf-8")
        result = parse(source)
        if not result.ok or result.tree is None:
            raise ReasonExternal(f"import {path!r}: parse failed").err()
        child_resolver = PathImportResolver(full_path.parent)
        return evaluate(result.tree, child_resolver)


# ── Binding resolution ────────────────────────────────────────────────────────


def _resolve_binding(binding_tagged: Tagged[Binding], value: GoldValue, ns: Namespace) -> None:
    b = binding_tagged.contents
    if isinstance(b, IdentifierBinding):
        ns.bind(b.name.contents, value)
    elif isinstance(b, ListPatternBinding):
        try:
            _resolve_list_binding(b.binding.contents, value, ns)
        except Error as e:
            raise e.tag(binding_tagged.span, Action.Bind)
    elif isinstance(b, MapPatternBinding):
        try:
            _resolve_map_binding(b.binding.contents, value, ns)
        except Error as e:
            raise e.tag(binding_tagged.span, Action.Bind)
    elif isinstance(b, MissingBinding):
        pass
    else:
        raise ReasonExternal(f"unknown binding type: {type(b).__name__!r}").err()


def _resolve_list_binding(lb: ListBinding, value: GoldValue, ns: Namespace) -> None:
    if not isinstance(value, list):
        raise UnpackTypeMismatch(BindingType.List, _type_of(value)).err()

    elements = lb.elements
    slurp_pos: int | None = next(
        (i for i, e in enumerate(elements) if isinstance(e.contents, (ListBindingSlurpTo, ListBindingSlurp))),
        None,
    )
    pre = elements[: slurp_pos if slurp_pos is not None else len(elements)]
    post = elements[slurp_pos + 1 :] if slurp_pos is not None else []

    required_pre = sum(
        1 for e in pre if isinstance(e.contents, ListBindingSingleton) and e.contents.default is None
    )
    required_post = sum(
        1 for e in post if isinstance(e.contents, ListBindingSingleton) and e.contents.default is None
    )
    if len(value) < required_pre + required_post:
        raise UnpackListTooShort().err()
    if slurp_pos is None and len(value) > len(pre) + len(post):
        raise UnpackListTooLong().err()

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
            raise UnpackListTooShort().err()

    if slurp_pos is not None:
        slurp = elements[slurp_pos].contents
        available = len(value) - idx
        actual_post = min(len(post), available)
        slurp_items = value[idx : len(value) - actual_post] if actual_post else value[idx:]
        if isinstance(slurp, ListBindingSlurpTo):
            ns.bind(slurp.name, list(slurp_items))

    for i, elem_tagged in enumerate(post):
        elem = elem_tagged.contents
        assert isinstance(elem, ListBindingSingleton)
        list_idx = len(value) - len(post) + i
        if list_idx >= idx:
            _resolve_binding(elem.binding, value[list_idx], ns)
        elif elem.default is not None:
            _resolve_binding(elem.binding, _eval_expr(elem.default, ns), ns)
        else:
            raise UnpackListTooShort().err()


def _resolve_map_binding(mb: MapBinding, value: GoldValue, ns: Namespace) -> None:
    if not isinstance(value, dict):
        raise UnpackTypeMismatch(BindingType.Map, _type_of(value)).err()

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
                raise UnpackKeyMissing(k).err().tag(elem.key.span, Action.Bind)
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


def _type_of(v: GoldValue) -> ObjectType:
    if v is None:
        return ObjectType.Null
    if isinstance(v, bool):
        return ObjectType.Boolean
    if isinstance(v, int):
        return ObjectType.Integer
    if isinstance(v, float):
        return ObjectType.Float
    if isinstance(v, str):
        return ObjectType.String
    if isinstance(v, list):
        return ObjectType.List
    if isinstance(v, dict):
        return ObjectType.Map
    return ObjectType.Function


# ── Eager binary operators ────────────────────────────────────────────────────


def _gold_eq(a: GoldValue, b: GoldValue) -> bool:
    if isinstance(a, bool) or isinstance(b, bool):
        return type(a) is type(b) and a == b
    if _is_int(a) and _is_int(b):
        return a == b
    if _is_numeric(a) and _is_numeric(b):
        return float(a) == float(b)
    return type(a) is type(b) and a == b


def _compare(a: GoldValue, b: GoldValue) -> int | None:
    if _is_numeric(a) and _is_numeric(b):
        fa, fb = float(a), float(b)
        return (fa > fb) - (fa < fb)
    if isinstance(a, str) and isinstance(b, str):
        return (a > b) - (a < b)
    return None


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
            raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Add)).err()

        case EagerOp.Subtract:
            if _is_int(lhs) and _is_int(rhs):
                return lhs - rhs
            if _is_numeric(lhs) and _is_numeric(rhs):
                return float(lhs) - float(rhs)
            raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Subtract)).err()

        case EagerOp.Multiply:
            if _is_int(lhs) and _is_int(rhs):
                return lhs * rhs
            if _is_numeric(lhs) and _is_numeric(rhs):
                return float(lhs) * float(rhs)
            raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Multiply)).err()

        case EagerOp.Divide:
            if not _is_numeric(lhs) or not _is_numeric(rhs):
                raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Divide)).err()
            if rhs == 0:
                raise ValueOutOfRange().err()
            return float(lhs) / float(rhs)

        case EagerOp.IntegerDivide:
            if not _is_int(lhs) or not _is_int(rhs):
                raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.IntegerDivide)).err()
            if rhs == 0:
                raise ValueOutOfRange().err()
            return lhs // rhs

        case EagerOp.Power:
            if not _is_numeric(lhs) or not _is_numeric(rhs):
                raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Power)).err()
            if _is_int(lhs) and _is_int(rhs) and rhs >= 0:
                return int(lhs) ** int(rhs)
            return float(lhs) ** float(rhs)

        case EagerOp.Less:
            c = _compare(lhs, rhs)
            if c is None:
                raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Less)).err()
            return c < 0

        case EagerOp.Greater:
            c = _compare(lhs, rhs)
            if c is None:
                raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Greater)).err()
            return c > 0

        case EagerOp.LessEqual:
            c = _compare(lhs, rhs)
            if c is None:
                raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.LessEqual)).err()
            return c <= 0

        case EagerOp.GreaterEqual:
            c = _compare(lhs, rhs)
            if c is None:
                raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.GreaterEqual)).err()
            return c >= 0

        case EagerOp.Equal:
            return _gold_eq(lhs, rhs)

        case EagerOp.NotEqual:
            return not _gold_eq(lhs, rhs)

        case EagerOp.Index:
            if isinstance(lhs, list) and _is_int(rhs):
                idx = int(rhs)
                if idx < 0 or idx >= len(lhs):
                    raise ValueOutOfRange().err()
                return lhs[idx]
            if isinstance(lhs, dict) and isinstance(rhs, str):
                if rhs not in lhs:
                    raise ReasonUnassigned(str(rhs)).err()
                return lhs[rhs]
            raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Index)).err()

        case EagerOp.Contains:
            # Gold syntax: container has element  (lhs=container, rhs=element)
            if isinstance(lhs, list):
                return any(_gold_eq(rhs, x) for x in lhs)
            if isinstance(lhs, str) and isinstance(rhs, str):
                return rhs in lhs
            raise TypeMismatchBinOp(_type_of(lhs), _type_of(rhs), str(EagerOp.Contains)).err()

    raise ReasonExternal(f"unknown op: {op!r}").err()


# ── Built-in functions ────────────────────────────────────────────────────────

_Builtin = Any  # Callable[[list[EvalValue], dict[str, EvalValue]], EvalValue]


def _builtin_len(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    x = args[0]
    if isinstance(x, str):
        return len(x)
    if isinstance(x, list):
        return len(x)
    if isinstance(x, dict):
        return len(x)
    raise TypeMismatchExpectedPosArg(
        0, (ObjectType.String, ObjectType.List, ObjectType.Map), _type_of(x)
    ).err()


def _builtin_range(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) not in (1, 2):
        raise TypeMismatchArgCount(1, 2, len(args)).err()
    if len(args) == 2:
        if not _is_int(args[0]):
            raise TypeMismatchExpectedPosArg(0, (ObjectType.Integer,), _type_of(args[0])).err()
        if not _is_int(args[1]):
            raise TypeMismatchExpectedPosArg(1, (ObjectType.Integer,), _type_of(args[1])).err()
        return list(range(int(args[0]), int(args[1])))
    if not _is_int(args[0]):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.Integer,), _type_of(args[0])).err()
    return list(range(int(args[0])))


def _builtin_int(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
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
            raise ValueConvert(ObjectType.Integer).err() from None
    raise TypeMismatchExpectedPosArg(
        0, (ObjectType.Integer, ObjectType.Float, ObjectType.Boolean, ObjectType.String), _type_of(x)
    ).err()


def _builtin_float(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
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
            raise ValueConvert(ObjectType.Float).err() from None
    raise TypeMismatchExpectedPosArg(
        0, (ObjectType.Integer, ObjectType.Float, ObjectType.Boolean, ObjectType.String), _type_of(x)
    ).err()


def _builtin_bool(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return _truthy(args[0])


def _builtin_str(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return _gold_str(args[0])


def _builtin_map_fn(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2:
        raise TypeMismatchArgCount(2, 2, len(args)).err()
    f, xs = args[0], args[1]
    if not isinstance(f, (GoldFunction, GoldBuiltin)):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.Function,), _type_of(f)).err()
    if not isinstance(xs, list):
        raise TypeMismatchExpectedPosArg(1, (ObjectType.List,), _type_of(xs)).err()
    return [_call(f, [x], {}) for x in xs]


def _builtin_filter_fn(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2:
        raise TypeMismatchArgCount(2, 2, len(args)).err()
    f, xs = args[0], args[1]
    if not isinstance(f, (GoldFunction, GoldBuiltin)):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.Function,), _type_of(f)).err()
    if not isinstance(xs, list):
        raise TypeMismatchExpectedPosArg(1, (ObjectType.List,), _type_of(xs)).err()
    return [x for x in xs if _truthy(_call(f, [x], {}))]


def _builtin_items(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    x = args[0]
    if not isinstance(x, dict):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.Map,), _type_of(x)).err()
    return [[k, v] for k, v in x.items()]


def _builtin_exp(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    x = args[0]
    if not _is_numeric(x):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.Integer, ObjectType.Float), _type_of(x)).err()
    xf = float(x)
    if "base" in kwargs:
        base = kwargs["base"]
        if not _is_numeric(base):
            raise TypeMismatchExpectedKwarg(
                "base", (ObjectType.Integer, ObjectType.Float), _type_of(base)
            ).err()
        return float(base) ** xf
    return math.exp(xf)


def _builtin_log(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    x = args[0]
    if not _is_numeric(x):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.Integer, ObjectType.Float), _type_of(x)).err()
    xf = float(x)
    if "base" in kwargs:
        base = kwargs["base"]
        if not _is_numeric(base):
            raise TypeMismatchExpectedKwarg(
                "base", (ObjectType.Integer, ObjectType.Float), _type_of(base)
            ).err()
        return math.log(xf, float(base))
    return math.log(xf)


def _builtin_ord(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    x = args[0]
    if not isinstance(x, str):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.String,), _type_of(x)).err()
    if len(x) != 1:
        raise ValueTooLong().err()
    return ord(x)


def _builtin_chr(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    x = args[0]
    if not _is_int(x):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.Integer,), _type_of(x)).err()
    try:
        return chr(int(x))
    except (ValueError, OverflowError) as e:
        raise ValueOutOfRange().err() from e


def _builtin_startswith(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2:
        raise TypeMismatchArgCount(2, 2, len(args)).err()
    x, y = args
    if not isinstance(x, str):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.String,), _type_of(x)).err()
    if not isinstance(y, str):
        raise TypeMismatchExpectedPosArg(1, (ObjectType.String,), _type_of(y)).err()
    return x.startswith(y)


def _builtin_endswith(args: list[GoldValue], kwargs: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 2:
        raise TypeMismatchArgCount(2, 2, len(args)).err()
    x, y = args
    if not isinstance(x, str):
        raise TypeMismatchExpectedPosArg(0, (ObjectType.String,), _type_of(x)).err()
    if not isinstance(y, str):
        raise TypeMismatchExpectedPosArg(1, (ObjectType.String,), _type_of(y)).err()
    return x.endswith(y)


def _builtin_isint(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return _is_int(args[0])


def _builtin_isstr(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return isinstance(args[0], str)


def _builtin_isnull(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return args[0] is None


def _builtin_isbool(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return isinstance(args[0], bool)


def _builtin_isfloat(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return _is_float(args[0])


def _builtin_isnumber(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return _is_numeric(args[0])


def _builtin_isobject(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return isinstance(args[0], dict)


def _builtin_islist(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return isinstance(args[0], list)


def _builtin_isfunc(args: list[GoldValue], _: dict[str, GoldValue]) -> GoldValue:
    if len(args) != 1:
        raise TypeMismatchArgCount(1, 1, len(args)).err()
    return isinstance(args[0], (GoldFunction, GoldBuiltin))


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
    raise TypeMismatchCall(_type_of(func)).err()


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
                raise TypeMismatchSplatArg(_type_of(val)).err().tag(a.expr.span, Action.Splat)
    return pos, kw


# ── List / map element helpers ────────────────────────────────────────────────


def _eval_list_element(elem_tagged: Tagged[Any], ns: Namespace) -> list[GoldValue]:
    e = elem_tagged.contents
    if isinstance(e, ListSingleton):
        return [_eval_expr(e.expr, ns)]
    if isinstance(e, ListSplat):
        val = _eval_expr(e.expr, ns)
        if not isinstance(val, list):
            raise TypeMismatchSplatList(_type_of(val)).err().tag(e.expr.span, Action.Splat)
        return val
    if isinstance(e, ListLoop):
        items = _eval_expr(e.iterable, ns)
        if not isinstance(items, list):
            raise TypeMismatchIterate(_type_of(items)).err().tag(e.iterable.span, Action.Iterate)
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
    raise ReasonExternal(f"unexpected list element type: {type(e).__name__!r}").err()


def _eval_map_element(elem_tagged: Tagged[Any], ns: Namespace) -> dict[str, GoldValue]:
    e = elem_tagged.contents
    if isinstance(e, MapSingleton):
        k = _eval_expr(e.key, ns)
        if not isinstance(k, str):
            raise TypeMismatchMapKey(_type_of(k)).err().tag(e.key.span, Action.Assign)
        return {k: _eval_expr(e.value, ns)}
    if isinstance(e, MapSplat):
        val = _eval_expr(e.expr, ns)
        if not isinstance(val, dict):
            raise TypeMismatchSplatMap(_type_of(val)).err().tag(e.expr.span, Action.Splat)
        return dict(val)
    if isinstance(e, MapLoop):
        items = _eval_expr(e.iterable, ns)
        if not isinstance(items, list):
            raise TypeMismatchIterate(_type_of(items)).err().tag(e.iterable.span, Action.Iterate)
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
    raise ReasonExternal(f"unexpected map element type: {type(e).__name__!r}").err()


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
                try:
                    if elem.fmt is not None:
                        parts.append(_format_value(v, elem.fmt))
                    else:
                        if isinstance(v, (list, dict, GoldFunction, GoldBuiltin)):
                            raise TypeMismatchInterpolate(_type_of(v)).err()
                        parts.append(_gold_str(v))
                except Error as e:
                    raise e.tag(elem.expr.span, Action.Format)
        return "".join(parts)

    if isinstance(node, IdentifierExpr):
        try:
            return ns.lookup(node.name.contents)
        except Error as e:
            raise e.tag(node.name.span, Action.LookupName)

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
            try:
                match t.op.contents:
                    case UnOp.ArithmeticalNegate:
                        if _is_int(val):
                            return -(val)
                        if _is_float(val):
                            return -(val)
                        raise TypeMismatchUnOp(_type_of(val), str(UnOp.ArithmeticalNegate)).err()
                    case UnOp.LogicalNegate:
                        return not _truthy(val)
            except Error as e:
                raise e.tag(t.op.span, Action.Evaluate)

        if isinstance(t, BinOpTransform):
            op = t.op.contents
            if isinstance(op, LogicOp):
                lhs = _eval_expr(node.operand, ns)
                if op == LogicOp.And:
                    return lhs if not _truthy(lhs) else _eval_expr(t.operand, ns)
                return lhs if _truthy(lhs) else _eval_expr(t.operand, ns)
            lhs = _eval_expr(node.operand, ns)
            rhs = _eval_expr(t.operand, ns)
            try:
                return _eval_eager_op(op, lhs, rhs)
            except Error as e:
                raise e.tag(t.op.span, Action.Evaluate)

        if isinstance(t, FunCallTransform):
            func = _eval_expr(node.operand, ns)
            pos_args, kw_args = _eval_args(t.args.contents, ns)
            try:
                return _call(func, pos_args, kw_args)
            except Error as e:
                raise e.tag(t.args.span, Action.Evaluate)

    if isinstance(node, MissingExpr):
        raise ReasonExternal("missing expression (parse error in source)").err()

    raise ReasonExternal(f"unexpected expression node: {type(node).__name__!r}").err()


# ── Root namespace ────────────────────────────────────────────────────────────


def _make_builtins_namespace() -> Namespace:
    ns = Namespace()
    for name in _BUILTIN_TABLE:
        ns.bind(name, GoldBuiltin(name=name))
    return ns


_BUILTINS_NS: Namespace = _make_builtins_namespace()


# ── Public API ────────────────────────────────────────────────────────────────


@dataclass
class EvalResult:
    value: GoldValue | None
    error: Error | None

    @property
    def ok(self) -> bool:
        return self.error is None

    def pprint(self, **kwargs: Unpack[PrintOpts]) -> str:
        return pprint_eval_result(self, **kwargs)


def evaluate(file: File, resolver: AbstractImportResolver | None = None) -> GoldValue:
    """Evaluate a parsed Gold ``File`` AST and return the result value."""
    ns = _BUILTINS_NS.child()

    for stmt in file.statements:
        if isinstance(stmt, ImportStatement):
            if resolver is None:
                raise ReasonExternal(f"import {stmt.path.contents!r}: no resolver provided").err()
            value = resolver.resolve(stmt.path.contents)
            _resolve_binding(stmt.binding, value, ns)

    return _eval_expr(file.expression, ns)


def evaluate_source(source: str, resolver: AbstractImportResolver | None = None) -> GoldValue:
    """Parse ``source`` and evaluate it, returning the result value."""
    result = parse(source)
    if not result.ok or result.tree is None:
        if result.errors:
            raise result.errors[0]
        raise ReasonExternal("parse failed").err()
    return evaluate(result.tree, resolver)


def evaluate_source_result(source: str, resolver: AbstractImportResolver | None = None) -> EvalResult:
    """Like ``evaluate_source`` but returns an ``EvalResult`` instead of raising."""
    try:
        return EvalResult(value=evaluate_source(source, resolver), error=None)
    except Error as e:
        return EvalResult(value=None, error=e)


def evaluate_file_result(path: Path) -> EvalResult:
    """Evaluate a Gold file (with import support) and return an ``EvalResult``."""
    try:
        source = path.read_text(encoding="utf-8")
        resolver = PathImportResolver(path.parent)
        return EvalResult(value=evaluate_source(source, resolver), error=None)
    except Error as e:
        return EvalResult(value=None, error=e)
