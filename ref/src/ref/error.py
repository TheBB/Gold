from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from pathlib import Path

    from .span import Span

# ── Type ──────────────────────────────────────────────────────────────────────


class Type(Enum):
    Integer = auto()
    Float = auto()
    String = auto()
    Boolean = auto()
    List = auto()
    Map = auto()
    Function = auto()
    Iterator = auto()
    Null = auto()

    def __str__(self) -> str:
        match self:
            case Type.Integer:
                return "int"
            case Type.Float:
                return "float"
            case Type.String:
                return "str"
            case Type.Boolean:
                return "bool"
            case Type.List:
                return "list"
            case Type.Map:
                return "map"
            case Type.Function:
                return "function"
            case Type.Iterator:
                return "iterator"
            case Type.Null:
                return "null"


# ── SyntaxElement ─────────────────────────────────────────────────────────────


class SyntaxElement(Enum):
    """Variants of SyntaxElement without payload."""

    ArgElement = "function argument"
    As = "'as'"
    Binding = "binding pattern"
    Else = "'else'"
    EndOfInput = "end of input"
    Expression = "expression"
    Identifier = "identifier"
    ImportPath = "import path"
    In = "'in'"
    KeywordParam = "keyword parameter"
    ListBindingElement = "list binding pattern"
    ListElement = "list element"
    MapBindingElement = "map binding pattern"
    MapElement = "map element"
    MapValue = "map value"
    Number = "number"
    Operand = "operand"
    PosParam = "positional parameter"
    Then = "'then'"
    Whitespace = "whitespace"

    def __str__(self) -> str:
        return self.value


@dataclass(frozen=True)
class SyntaxElementToken:
    """The Token(TokenType) variant of SyntaxElement."""

    token_type: Any  # TokenType at runtime

    def __str__(self) -> str:
        return str(self.token_type)


type AnySyntaxElement = SyntaxElement | SyntaxElementToken


# ── Syntax ────────────────────────────────────────────────────────────────────


class AbstractSyntax:
    """Base for all Syntax error variants."""


@dataclass(frozen=True)
class SyntaxUnexpectedEof(AbstractSyntax):
    def __str__(self) -> str:
        return "unexpected end of input"


@dataclass(frozen=True)
class SyntaxUnexpectedChar(AbstractSyntax):
    char: str

    def __str__(self) -> str:
        return f"unexpected {self.char}"


@dataclass(frozen=True)
class SyntaxExpectedOne(AbstractSyntax):
    element: AnySyntaxElement

    def __str__(self) -> str:
        return f"expected {self.element}"


@dataclass(frozen=True)
class SyntaxExpectedTwo(AbstractSyntax):
    element1: AnySyntaxElement
    element2: AnySyntaxElement

    def __str__(self) -> str:
        return f"expected {self.element1} or {self.element2}"


@dataclass(frozen=True)
class SyntaxExpectedThree(AbstractSyntax):
    element1: AnySyntaxElement
    element2: AnySyntaxElement
    element3: AnySyntaxElement

    def __str__(self) -> str:
        return f"expected {self.element1}, {self.element2} or {self.element3}"


@dataclass(frozen=True)
class SyntaxMultiSlurp(AbstractSyntax):
    def __str__(self) -> str:
        return "only one slurp allowed in this context"


@dataclass(frozen=True)
class SyntaxDefaultSequence(AbstractSyntax):
    def __str__(self) -> str:
        return "binding without default value follows binding with default value"


type Syntax = (
    SyntaxUnexpectedEof
    | SyntaxUnexpectedChar
    | SyntaxExpectedOne
    | SyntaxExpectedTwo
    | SyntaxExpectedThree
    | SyntaxMultiSlurp
    | SyntaxDefaultSequence
)


# ── BindingType ───────────────────────────────────────────────────────────────


class BindingType(Enum):
    Identifier = "identifier"
    List = "list"
    Map = "map"

    def __str__(self) -> str:
        return self.value


# ── Unpack ────────────────────────────────────────────────────────────────────


class AbstractUnpack:
    """Base for all Unpack error variants."""


@dataclass(frozen=True)
class UnpackListTooShort(AbstractUnpack):
    def __str__(self) -> str:
        return "list too short"


@dataclass(frozen=True)
class UnpackListTooLong(AbstractUnpack):
    def __str__(self) -> str:
        return "list too long"


@dataclass(frozen=True)
class UnpackKeyMissing(AbstractUnpack):
    key: str

    def __str__(self) -> str:
        return f"unbound key '{self.key}'"


@dataclass(frozen=True)
class UnpackTypeMismatch(AbstractUnpack):
    expected: BindingType
    got: Type

    def __str__(self) -> str:
        return f"expected {self.expected}, found {self.got}"


type Unpack = UnpackListTooShort | UnpackListTooLong | UnpackKeyMissing | UnpackTypeMismatch


# ── TypeMismatch ──────────────────────────────────────────────────────────────


class AbstractTypeMismatch:
    """Base for all TypeMismatch error variants."""


@dataclass(frozen=True)
class TypeMismatchIterate(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"non-iterable type: {self.got}"


@dataclass(frozen=True)
class TypeMismatchSplatList(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for splatting: {self.got}"


@dataclass(frozen=True)
class TypeMismatchSplatMap(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for splatting: {self.got}"


@dataclass(frozen=True)
class TypeMismatchSplatArg(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for splatting: {self.got}"


@dataclass(frozen=True)
class TypeMismatchMapKey(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for map key: {self.got}"


@dataclass(frozen=True)
class TypeMismatchInterpolate(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for interpolation: {self.got}"


@dataclass(frozen=True)
class TypeMismatchInterpolateSpec(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for format spec: {self.got}"


@dataclass(frozen=True)
class TypeMismatchBinOp(AbstractTypeMismatch):
    left: Type
    right: Type
    op: str

    def __str__(self) -> str:
        return f"unsuitable types for '{self.op}': {self.left} and {self.right}"


@dataclass(frozen=True)
class TypeMismatchUnOp(AbstractTypeMismatch):
    got: Type
    op: str

    def __str__(self) -> str:
        return f"unsuitable type for '{self.op}': {self.got}"


@dataclass(frozen=True)
class TypeMismatchCall(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for function call: {self.got}"


@dataclass(frozen=True)
class TypeMismatchJson(AbstractTypeMismatch):
    got: Type

    def __str__(self) -> str:
        return f"unsuitable type for JSON-like conversion: {self.got}"


def _fmt_expected_arg(name: object, allowed: tuple[Type, ...], received: Type) -> str:
    prefix = f"unsuitable type for parameter {name} - expected "
    if len(allowed) == 0:
        suffix = ""
    elif len(allowed) == 1:
        suffix = str(allowed[0])
    else:
        suffix = ", ".join(str(t) for t in allowed[:-1]) + f" or {allowed[-1]}"
    return prefix + suffix + f", got {received}"


@dataclass(frozen=True)
class TypeMismatchExpectedPosArg(AbstractTypeMismatch):
    index: int
    allowed: tuple[Type, ...]
    received: Type

    def __str__(self) -> str:
        return _fmt_expected_arg(self.index + 1, self.allowed, self.received)


@dataclass(frozen=True)
class TypeMismatchExpectedKwarg(AbstractTypeMismatch):
    name: str
    allowed: tuple[Type, ...]
    received: Type

    def __str__(self) -> str:
        return _fmt_expected_arg(self.name, self.allowed, self.received)


@dataclass(frozen=True)
class TypeMismatchArgCount(AbstractTypeMismatch):
    low: int
    high: int
    received: int

    def __str__(self) -> str:
        if self.low == self.high == 1:
            return f"expected 1 argument, got {self.received}"
        if self.low == self.high:
            return f"expected {self.low} arguments, got {self.received}"
        return f"expected {self.low} to {self.high} arguments, got {self.received}"


type TypeMismatch = (
    TypeMismatchIterate
    | TypeMismatchSplatList
    | TypeMismatchSplatMap
    | TypeMismatchSplatArg
    | TypeMismatchMapKey
    | TypeMismatchInterpolate
    | TypeMismatchInterpolateSpec
    | TypeMismatchBinOp
    | TypeMismatchUnOp
    | TypeMismatchCall
    | TypeMismatchJson
    | TypeMismatchExpectedPosArg
    | TypeMismatchExpectedKwarg
    | TypeMismatchArgCount
)


# ── Value ─────────────────────────────────────────────────────────────────────


class AbstractValue:
    """Base for all Value error variants."""


@dataclass(frozen=True)
class ValueOutOfRange(AbstractValue):
    def __str__(self) -> str:
        return "value out of range"


@dataclass(frozen=True)
class ValueTooLarge(AbstractValue):
    def __str__(self) -> str:
        return "value too large"


@dataclass(frozen=True)
class ValueTooLong(AbstractValue):
    def __str__(self) -> str:
        return "value too long"


@dataclass(frozen=True)
class ValueConvert(AbstractValue):
    to: Type

    def __str__(self) -> str:
        return f"couldn't convert to {self.to}"


type Value = ValueOutOfRange | ValueTooLarge | ValueTooLong | ValueConvert


# ── FileSystem ────────────────────────────────────────────────────────────────


class AbstractFileSystem:
    """Base for all FileSystem error variants."""


@dataclass(frozen=True)
class FileSystemNoParent(AbstractFileSystem):
    path: Path

    def __str__(self) -> str:
        return f"path has no parent: {self.path}"


@dataclass(frozen=True)
class FileSystemRead(AbstractFileSystem):
    path: Path

    def __str__(self) -> str:
        return f"couldn't read file: {self.path}"


type FileSystem = FileSystemNoParent | FileSystemRead


# ── Reason ────────────────────────────────────────────────────────────────────


class AbstractReason:
    """Base for all Reason variants."""


@dataclass(frozen=True)
class ReasonSyntax(AbstractReason):
    syntax: Syntax

    def __str__(self) -> str:
        return str(self.syntax)


@dataclass(frozen=True)
class ReasonUnbound(AbstractReason):
    name: str

    def __str__(self) -> str:
        return f"unbound name '{self.name}'"


@dataclass(frozen=True)
class ReasonUnassigned(AbstractReason):
    key: str

    def __str__(self) -> str:
        return f"unbound key '{self.key}'"


@dataclass(frozen=True)
class ReasonUnpack(AbstractReason):
    unpack: Unpack

    def __str__(self) -> str:
        return str(self.unpack)


@dataclass(frozen=True)
class ReasonExternal(AbstractReason):
    message: str

    def __str__(self) -> str:
        return f"external error: {self.message}"


@dataclass(frozen=True)
class ReasonTypeMismatch(AbstractReason):
    mismatch: TypeMismatch

    def __str__(self) -> str:
        return str(self.mismatch)


@dataclass(frozen=True)
class ReasonValue(AbstractReason):
    value: Value

    def __str__(self) -> str:
        return str(self.value)


@dataclass(frozen=True)
class ReasonFileSystem(AbstractReason):
    fs: FileSystem

    def __str__(self) -> str:
        return str(self.fs)


@dataclass(frozen=True)
class ReasonUnknownImport(AbstractReason):
    path: str

    def __str__(self) -> str:
        return f"unknown import: '{self.path}'"


type Reason = (
    ReasonSyntax
    | ReasonUnbound
    | ReasonUnassigned
    | ReasonUnpack
    | ReasonExternal
    | ReasonTypeMismatch
    | ReasonValue
    | ReasonFileSystem
    | ReasonUnknownImport
)


# ── Action ────────────────────────────────────────────────────────────────────


class Action(Enum):
    Parse = "parsing"
    LookupName = "evaluating"
    Bind = "pattern matching"
    Slurp = "slurping"
    Splat = "splatting"
    Iterate = "iterating"
    Assign = "assigning"
    Import = "importing"
    Evaluate = "evaluating"
    Format = "interpolating"

    def __str__(self) -> str:
        return self.value


# ── Error ─────────────────────────────────────────────────────────────────────


class Error(Exception):
    """Grand unified error type for the Gold pipeline."""

    reason: Reason | None
    locations: list[tuple[Span, Action]]
    rendered: str | None

    def __init__(
        self,
        reason: Reason | None = None,
        locations: list[tuple[Span, Action]] | None = None,
        rendered: str | None = None,
    ) -> None:
        self.reason = reason
        self.locations = locations if locations is not None else []
        self.rendered = rendered
        super().__init__()

    @classmethod
    def new(cls, reason: Reason) -> Error:
        return cls(reason=reason)

    def tag(self, span: Span, action: Action) -> Error:
        """Append a (span, action) pair to the location stack."""
        self.locations.append((span, action))
        return self

    def with_reason(self, reason: Reason) -> Error:
        self.reason = reason
        return self

    def render(self, code: str | None = None) -> Error:
        if self.rendered is None:
            self.rendered = self._format(code)
        return self

    def _format(self, code: str | None) -> str:
        reason_str = (
            str(self.reason)
            if self.reason is not None
            else "internal error 002 - this should not happen, please file a bug report"
        )
        parts = [f"Error: {reason_str}"]
        for span, action in self.locations:
            if code is not None:
                bol = span.offset - span.column
                eol_idx = code[bol + 1 :].find("\n")
                eol = (bol + 1 + eol_idx) if eol_idx != -1 else len(code)
                span_end = min(span.offset + span.length, eol) - span.offset
                parts.append("\n" + code[bol:eol])
                parts.append("\n" + " " * span.column + "^" * span_end)
            parts.append(f"\nwhile {action} at {span.line + 1}:{span.column + 1}")
        return "".join(parts)

    @property
    def span(self) -> Span | None:
        """First recorded span, for backwards-compat access."""
        return self.locations[0][0] if self.locations else None

    @property
    def message(self) -> str:
        """Reason string, for backwards-compat access."""
        return str(self.reason) if self.reason is not None else ""

    def __str__(self) -> str:
        if self.rendered is not None:
            return self.rendered
        return self._format(None)

    def __repr__(self) -> str:
        return f"Error(reason={self.reason!r}, locations={self.locations!r})"
