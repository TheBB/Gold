from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import Enum, auto
from typing import TYPE_CHECKING


if TYPE_CHECKING:
    from .evaluation import Namespace
    from .span import Tagged


# ── Values ─────────────────────────────────────────────────────────────────


@dataclass
class GoldFunction:
    """A Gold closure: parameter bindings, body AST, and captured scope."""

    positional: ListBinding
    keywords: MapBinding | None
    body: Tagged[Expr]
    captured: Namespace


@dataclass(frozen=True)
class GoldBuiltin:
    """A named built-in function."""

    name: str


type GoldValue = (
    int
    | float
    | str
    | bool
    | None
    | Mapping[str, GoldValue]
    | Sequence[GoldValue]
    | GoldFunction
    | GoldBuiltin
)

# ── Operators ─────────────────────────────────────────────────────────────────


class UnOp(Enum):
    ArithmeticalNegate = auto()
    LogicalNegate = auto()

    def __str__(self) -> str:
        match self:
            case UnOp.ArithmeticalNegate:
                return "-"
            case UnOp.LogicalNegate:
                return "not"


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

    def __str__(self) -> str:
        match self:
            case EagerOp.Index:
                return "subscript"
            case EagerOp.Power:
                return "^"
            case EagerOp.Multiply:
                return "*"
            case EagerOp.IntegerDivide:
                return "//"
            case EagerOp.Divide:
                return "/"
            case EagerOp.Add:
                return "+"
            case EagerOp.Subtract:
                return "-"
            case EagerOp.Less:
                return "<"
            case EagerOp.Greater:
                return ">"
            case EagerOp.LessEqual:
                return "<="
            case EagerOp.GreaterEqual:
                return ">="
            case EagerOp.Equal:
                return "=="
            case EagerOp.NotEqual:
                return "!="
            case EagerOp.Contains:
                return "in"


class LogicOp(Enum):
    And = auto()
    Or = auto()

    def __str__(self) -> str:
        match self:
            case LogicOp.And:
                return "and"
            case LogicOp.Or:
                return "or"


# In Rust: BinOp = Eager(EagerOp) | Logic(LogicOp). In Python a plain union suffices.
type BinOp = EagerOp | LogicOp


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


class AbstractListBindingElement:
    """Base for elements inside a list pattern."""


@dataclass(frozen=True)
class ListBindingSingleton(AbstractListBindingElement):
    """An ordinary sub-pattern with an optional default value."""

    binding: Tagged[Binding]
    default: Tagged[Expr] | None = None


@dataclass(frozen=True)
class ListBindingSlurpTo(AbstractListBindingElement):
    """Collect remaining list elements into a named binding."""

    name: str


@dataclass(frozen=True)
class ListBindingSlurp(AbstractListBindingElement):
    """Consume remaining list elements, discarding them."""


class AbstractMapBindingElement:
    """Base for elements inside a map pattern."""


@dataclass(frozen=True)
class MapBindingSingleton(AbstractMapBindingElement):
    """A key matched to a sub-pattern, with an optional default value."""

    key: Tagged[str]
    binding: Tagged[Binding]
    default: Tagged[Expr] | None = None


@dataclass(frozen=True)
class MapBindingSlurpTo(AbstractMapBindingElement):
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


class AbstractBinding:
    """Base for all pattern/binding forms."""


@dataclass(frozen=True)
class IdentifierBinding(AbstractBinding):
    """A simple named binding."""

    name: Tagged[str]


@dataclass(frozen=True)
class ListPatternBinding(AbstractBinding):
    """A list-destructuring binding."""

    binding: Tagged[ListBinding]


@dataclass(frozen=True)
class MapPatternBinding(AbstractBinding):
    """A map-destructuring binding."""

    binding: Tagged[MapBinding]


@dataclass(frozen=True)
class MissingBinding(AbstractBinding):
    """Sentinel used in error recovery when a required binding could not be parsed."""


# ── String elements ───────────────────────────────────────────────────────────


class AbstractStringElement:
    """Base for elements of an interpolated string."""


@dataclass(frozen=True)
class StringRaw(AbstractStringElement):
    """A literal chunk of string text."""

    value: str


@dataclass(frozen=True)
class StringInterpolate(AbstractStringElement):
    """An interpolated expression with an optional format spec."""

    expr: Tagged[Expr]
    fmt: FormatSpec | None = None


# ── List elements ─────────────────────────────────────────────────────────────


class AbstractListElement:
    """Base for elements of a list literal."""


@dataclass(frozen=True)
class ListSingleton(AbstractListElement):
    """A single value expression."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class ListSplat(AbstractListElement):
    """Spread an iterable into the list."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class ListLoop(AbstractListElement):
    """A for-comprehension that produces list elements."""

    binding: Tagged[Binding]
    iterable: Tagged[Expr]
    element: Tagged[ListElement]


@dataclass(frozen=True)
class ListCond(AbstractListElement):
    """A conditional element (if-guard) in a list literal."""

    condition: Tagged[Expr]
    element: Tagged[ListElement]


# ── Map elements ──────────────────────────────────────────────────────────────


class AbstractMapElement:
    """Base for elements of a map literal."""


@dataclass(frozen=True)
class MapSingleton(AbstractMapElement):
    """A single key→value pair."""

    key: Tagged[Expr]
    value: Tagged[Expr]


@dataclass(frozen=True)
class MapSplat(AbstractMapElement):
    """Merge another map into this literal."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class MapLoop(AbstractMapElement):
    """A for-comprehension that produces map entries."""

    binding: Tagged[Binding]
    iterable: Tagged[Expr]
    element: Tagged[MapElement]


@dataclass(frozen=True)
class MapCond(AbstractMapElement):
    """A conditional element (if-guard) in a map literal."""

    condition: Tagged[Expr]
    element: Tagged[MapElement]


# ── Argument elements ─────────────────────────────────────────────────────────


class AbstractArgElement:
    """Base for elements of a function call argument list."""


@dataclass(frozen=True)
class ArgSingleton(AbstractArgElement):
    """A positional argument."""

    expr: Tagged[Expr]


@dataclass(frozen=True)
class ArgKeyword(AbstractArgElement):
    """A named (keyword) argument."""

    key: Tagged[str]
    expr: Tagged[Expr]


@dataclass(frozen=True)
class ArgSplat(AbstractArgElement):
    """A splatted argument (list splat or map splat depending on runtime type)."""

    expr: Tagged[Expr]


# ── Transforms ────────────────────────────────────────────────────────────────


class AbstractTransform:
    """Base for expression transforms (operand → result)."""


@dataclass(frozen=True)
class UnOpTransform(AbstractTransform):
    """A unary operator. None means the identity/pass-through (Rust: Tagged<Option<UnOp>>)."""

    op: Tagged[UnOp | None]


@dataclass(frozen=True)
class BinOpTransform(AbstractTransform):
    """A binary operator with its right-hand operand."""

    op: Tagged[BinOp]
    operand: Tagged[Expr]


@dataclass(frozen=True)
class FunCallTransform(AbstractTransform):
    """A function call with its argument list."""

    args: Tagged[list[Tagged[ArgElement]]]


# ── Expressions ───────────────────────────────────────────────────────────────


class AbstractExpr:
    """Base for all expression AST nodes."""


@dataclass(frozen=True)
class LiteralExpr(AbstractExpr):
    """A scalar literal value (int, float, bool, str, or null)."""

    value: GoldValue


@dataclass(frozen=True)
class StringExpr(AbstractExpr):
    """An interpolated string (contains at least one interpolation)."""

    elements: list[StringElement]


@dataclass(frozen=True)
class IdentifierExpr(AbstractExpr):
    """A name looked up in the current scope."""

    name: Tagged[str]


@dataclass(frozen=True)
class ListExpr(AbstractExpr):
    """A list literal."""

    elements: list[Tagged[ListElement]]


@dataclass(frozen=True)
class MapExpr(AbstractExpr):
    """A map literal."""

    elements: list[Tagged[MapElement]]


@dataclass(frozen=True)
class LetExpr(AbstractExpr):
    """A let-block: bind patterns to expressions, then evaluate a body."""

    bindings: list[tuple[Tagged[Binding], Tagged[Expr]]]
    expression: Tagged[Expr]


@dataclass(frozen=True)
class TransformedExpr(AbstractExpr):
    """An operand with a transform applied (binary op, unary op, or function call)."""

    operand: Tagged[Expr]
    transform: Transform


@dataclass(frozen=True)
class FunctionExpr(AbstractExpr):
    """A function (lambda) definition."""

    positional: Tagged[ListBinding]
    keywords: Tagged[MapBinding] | None
    expression: Tagged[Expr]


@dataclass(frozen=True)
class BranchExpr(AbstractExpr):
    """An if/else conditional expression. Gold has no else-less branches."""

    condition: Tagged[Expr]
    true_branch: Tagged[Expr]
    false_branch: Tagged[Expr]


@dataclass(frozen=True)
class MissingExpr(AbstractExpr):
    """Sentinel used in error recovery when a required expression could not be parsed."""


# ── Top-level statements ──────────────────────────────────────────────────────


class AbstractTopLevel:
    """Base for file-scope statements (currently only imports)."""


@dataclass(frozen=True)
class ImportStatement(AbstractTopLevel):
    """Import a Gold file and bind its value to a pattern."""

    path: Tagged[str]
    binding: Tagged[Binding]


# ── File ──────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class File:
    """The root AST node for a Gold source file."""

    statements: list[TopLevel]
    expression: Tagged[Expr]


# ── Union type aliases ────────────────────────────────────────────────────────
# Use these in type hints for exhaustiveness checking.
# Use the Abstract* base classes for isinstance() checks at runtime.

type ListBindingElement = ListBindingSingleton | ListBindingSlurpTo | ListBindingSlurp
type MapBindingElement = MapBindingSingleton | MapBindingSlurpTo
type Binding = IdentifierBinding | ListPatternBinding | MapPatternBinding | MissingBinding
type StringElement = StringRaw | StringInterpolate
type ListElement = ListSingleton | ListSplat | ListLoop | ListCond
type MapElement = MapSingleton | MapSplat | MapLoop | MapCond
type ArgElement = ArgSingleton | ArgKeyword | ArgSplat
type Transform = UnOpTransform | BinOpTransform | FunCallTransform
type Expr = (
    LiteralExpr
    | StringExpr
    | IdentifierExpr
    | ListExpr
    | MapExpr
    | LetExpr
    | TransformedExpr
    | FunctionExpr
    | BranchExpr
    | MissingExpr
)
type TopLevel = ImportStatement
