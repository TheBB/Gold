from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .span import Tagged

# ── Primitive value types ─────────────────────────────────────────────────────

type GoldValue = int | float | str | bool | None | dict[str, GoldValue] | list[GoldValue]


# ── Operators ─────────────────────────────────────────────────────────────────


class UnOp(Enum):
    ArithmeticalNegate = auto()
    LogicalNegate = auto()


class EagerOp(Enum):
    Index = auto()
    Power = auto()
    Multiply = auto()
    IntegerDivide = auto()
    Divide = auto()
    Add = auto()
    Subtract = auto()
    Less = auto()
    Greater = auto()
    LessEqual = auto()
    GreaterEqual = auto()
    Equal = auto()
    NotEqual = auto()
    Contains = auto()


class LogicOp(Enum):
    And = auto()
    Or = auto()


# In Rust: BinOp = Eager(EagerOp) | Logic(LogicOp). In Python a plain union suffices.
BinOp = EagerOp | LogicOp


# ── Format spec ───────────────────────────────────────────────────────────────


class AlignSpec(Enum):
    Left = auto()
    Right = auto()
    Center = auto()
    AfterSign = auto()  # Rust: AlignSpec::AfterSign (the '=' fill)


class SignSpec(Enum):
    Plus = auto()
    Minus = auto()
    Space = auto()


class GroupingSpec(Enum):
    Comma = auto()
    Underscore = auto()


class FormatTypeSpec(Enum):
    """Flattened form of Rust's FormatType / IntegerFormatType / FloatFormatType."""
    String = auto()
    # integer subtypes
    Binary = auto()
    Character = auto()
    Decimal = auto()
    Octal = auto()
    HexLower = auto()
    HexUpper = auto()
    # float subtypes
    SciLower = auto()
    SciUpper = auto()
    Fixed = auto()
    General = auto()
    Percentage = auto()


@dataclass(frozen=True)
class FormatSpec:
    fill: str = " "
    align: AlignSpec | None = None
    sign: SignSpec | None = None
    alternate: bool = False
    width: int | None = None
    grouping: GroupingSpec | None = None
    precision: int | None = None
    fmt_type: FormatTypeSpec | None = None


# ── Bindings (patterns) ───────────────────────────────────────────────────────


class ListBindingElement:
    """Base for elements inside a list pattern."""


@dataclass(frozen=True)
class ListBEBinding(ListBindingElement):
    """An ordinary sub-pattern with an optional default value."""

    binding: Tagged[Binding]
    default: Tagged[Expr] | None = None


@dataclass(frozen=True)
class ListBESlurpTo(ListBindingElement):
    """Collect remaining list elements into a named binding."""

    name: str


@dataclass(frozen=True)
class ListBESlurp(ListBindingElement):
    """Consume remaining list elements, discarding them."""


class MapBindingElement:
    """Base for elements inside a map pattern."""


@dataclass(frozen=True)
class MapBEBinding(MapBindingElement):
    """A key matched to a sub-pattern, with an optional default value."""

    key: Tagged[str]
    binding: Tagged[Binding]
    default: Tagged[Expr] | None = None


@dataclass(frozen=True)
class MapBESlurpTo(MapBindingElement):
    """Collect remaining map entries into a named binding."""

    name: str


@dataclass(frozen=True)
class ListBinding:
    """A list-destructuring pattern."""

    elements: list[Tagged[ListBindingElement]]


@dataclass(frozen=True)
class MapBinding:
    """A map-destructuring pattern."""

    elements: list[Tagged[MapBindingElement]]


class Binding:
    """Base for all pattern/binding forms."""


@dataclass(frozen=True)
class IdentifierBinding(Binding):
    """A simple named binding."""

    name: Tagged[str]


@dataclass(frozen=True)
class ListPatternBinding(Binding):
    """A list-destructuring binding."""

    binding: Tagged[ListBinding]


@dataclass(frozen=True)
class MapPatternBinding(Binding):
    """A map-destructuring binding."""

    binding: Tagged[MapBinding]


# ── String elements ───────────────────────────────────────────────────────────


class StringElement:
    """Base for elements of an interpolated string."""


@dataclass(frozen=True)
class RawStringElement(StringElement):
    """A literal chunk of string text."""

    value: str


@dataclass(frozen=True)
class InterpolateStringElement(StringElement):
    """An interpolated expression with an optional format spec."""

    expr: Tagged[Expr]
    fmt: FormatSpec | None = None


# ── List elements ─────────────────────────────────────────────────────────────


class ListElement:
    """Base for elements of a list literal."""


@dataclass(frozen=True)
class SingletonLE(ListElement):
    """A single value expression."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class SplatLE(ListElement):
    """Spread an iterable into the list."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class LoopLE(ListElement):
    """A for-comprehension that produces list elements."""

    binding: Tagged[Binding]
    iterable: Tagged[Expr]
    element: Tagged[ListElement]


@dataclass(frozen=True)
class CondLE(ListElement):
    """A conditional element (if-guard) in a list literal."""

    condition: Tagged[Expr]
    element: Tagged[ListElement]


# ── Map elements ──────────────────────────────────────────────────────────────


class MapElement:
    """Base for elements of a map literal."""


@dataclass(frozen=True)
class SingletonME(MapElement):
    """A single key→value pair."""

    key: Tagged[Expr]
    value: Tagged[Expr]


@dataclass(frozen=True)
class SplatME(MapElement):
    """Merge another map into this literal."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class LoopME(MapElement):
    """A for-comprehension that produces map entries."""

    binding: Tagged[Binding]
    iterable: Tagged[Expr]
    element: Tagged[MapElement]


@dataclass(frozen=True)
class CondME(MapElement):
    """A conditional element (if-guard) in a map literal."""

    condition: Tagged[Expr]
    element: Tagged[MapElement]


# ── Argument elements ─────────────────────────────────────────────────────────


class ArgElement:
    """Base for elements of a function call argument list."""


@dataclass(frozen=True)
class SingletonAE(ArgElement):
    """A positional argument."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class KeywordAE(ArgElement):
    """A named (keyword) argument."""

    key: Tagged[str]
    expr: Tagged[Expr]


@dataclass(frozen=True)
class SplatAE(ArgElement):
    """A splatted argument (list splat or map splat depending on runtime type)."""

    expr: Tagged[Expr]


# ── Transforms ────────────────────────────────────────────────────────────────


class Transform:
    """Base for expression transforms (operand → result)."""


@dataclass(frozen=True)
class UnOpTransform(Transform):
    """A unary operator. None means the identity/pass-through (Rust: Tagged<Option<UnOp>>)."""

    op: Tagged[UnOp | None]


@dataclass(frozen=True)
class BinOpTransform(Transform):
    """A binary operator with its right-hand operand."""

    op: Tagged[BinOp]
    operand: Tagged[Expr]


@dataclass(frozen=True)
class FunCallTransform(Transform):
    """A function call with its argument list."""

    args: Tagged[list[Tagged[ArgElement]]]


# ── Expressions ───────────────────────────────────────────────────────────────


class Expr:
    """Base for all expression AST nodes."""


@dataclass(frozen=True)
class LiteralExpr(Expr):
    """A scalar literal value (int, float, bool, str, or null)."""

    value: GoldValue


@dataclass(frozen=True)
class StringExpr(Expr):
    """An interpolated string (contains at least one interpolation)."""

    elements: list[StringElement]


@dataclass(frozen=True)
class IdentifierExpr(Expr):
    """A name looked up in the current scope."""

    name: Tagged[str]


@dataclass(frozen=True)
class ListExpr(Expr):
    """A list literal."""

    elements: list[Tagged[ListElement]]


@dataclass(frozen=True)
class MapExpr(Expr):
    """A map literal."""

    elements: list[Tagged[MapElement]]


@dataclass(frozen=True)
class LetExpr(Expr):
    """A let-block: bind patterns to expressions, then evaluate a body."""

    bindings: list[tuple[Tagged[Binding], Tagged[Expr]]]
    expression: Tagged[Expr]


@dataclass(frozen=True)
class TransformedExpr(Expr):
    """An operand with a transform applied (binary op, unary op, or function call)."""

    operand: Tagged[Expr]
    transform: Transform


@dataclass(frozen=True)
class FunctionExpr(Expr):
    """A function (lambda) definition."""

    positional: Tagged[ListBinding]
    keywords: Tagged[MapBinding] | None
    expression: Tagged[Expr]


@dataclass(frozen=True)
class BranchExpr(Expr):
    """An if/else conditional expression. Gold has no else-less branches."""

    condition: Tagged[Expr]
    true_branch: Tagged[Expr]
    false_branch: Tagged[Expr]


# ── Top-level statements ──────────────────────────────────────────────────────


class TopLevel:
    """Base for file-scope statements (currently only imports)."""


@dataclass(frozen=True)
class ImportStatement(TopLevel):
    """Import a Gold file and bind its value to a pattern."""

    path: Tagged[str]
    binding: Tagged[Binding]


# ── File ──────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class File:
    """The root AST node for a Gold source file."""

    statements: list[TopLevel]
    expression: Tagged[Expr]
