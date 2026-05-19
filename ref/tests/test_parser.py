from __future__ import annotations

from typing import TYPE_CHECKING


if TYPE_CHECKING:
    from ref.error import Error

from ref.ast import (
    AlignSpec,
    ArgKeyword,
    ArgSingleton,
    ArgSplat,
    BinOpTransform,
    BranchExpr,
    EagerOp,
    Expr,
    FormatSpec,
    FormatTypeSpec,
    FunCallTransform,
    FunctionExpr,
    GoldValue,
    GroupingSpec,
    IdentifierBinding,
    IdentifierExpr,
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
    MapCond,
    MapExpr,
    MapLoop,
    MapPatternBinding,
    MapSingleton,
    MapSplat,
    SignSpec,
    StringExpr,
    StringInterpolate,
    StringRaw,
    TransformedExpr,
    UnOp,
    UnOpTransform,
)
from ref.parser import parse
from ref.span import Span, Tagged, tag


# ── Span helpers ──────────────────────────────────────────────────────────────


def S(start: int, end: int | None = None) -> Span:
    """S(n) = one-char span at offset n.  S(a, b) = span from a to b (length b-a)."""
    if end is None:
        return Span.from_offset(start)
    return Span.from_offsets(start, end)


# ── Expression / binding builders ─────────────────────────────────────────────


def lit(value: GoldValue, start: int, end: int | None = None) -> Tagged[LiteralExpr]:
    return tag(LiteralExpr(value), S(start, end))


def ident(name: str, start: int, end: int | None = None) -> Tagged[IdentifierExpr]:
    sp = S(start, end)
    return tag(IdentifierExpr(name=tag(name, sp)), sp)


def bid(name: str, start: int, end: int | None = None) -> Tagged[IdentifierBinding]:
    sp = S(start, end)
    return tag(IdentifierBinding(name=tag(name, sp)), sp)


def lel(value: GoldValue, start: int, end: int | None = None) -> Tagged[ListSingleton]:
    e = lit(value, start, end)
    return tag(ListSingleton(expr=e), e.span)


def retag[T](inner: Tagged[T], start: int, end: int | None = None) -> Tagged[T]:
    """Re-tag a Tagged expression with a new span (e.g. to add paren span)."""
    return tag(inner.contents, S(start, end))


def mel(key: Tagged[Expr], value: Tagged[Expr]) -> Tagged[MapSingleton]:
    return tag(MapSingleton(key=key, value=value), Span.covering(key.span, value.span))


def binop(
    lhs: Tagged[Expr],
    op: EagerOp | LogicOp,
    op_start: int,
    op_end: int | None,
    rhs: Tagged[Expr],
) -> Tagged[TransformedExpr]:
    return tag(
        TransformedExpr(operand=lhs, transform=BinOpTransform(op=tag(op, S(op_start, op_end)), operand=rhs)),
        Span.covering(lhs.span, rhs.span),
    )


def unop(
    operand: Tagged[Expr],
    op: UnOp | None,
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    op_span = S(op_start, op_end)
    return tag(
        TransformedExpr(operand=operand, transform=UnOpTransform(op=tag(op, op_span))),
        Span.covering(op_span, operand.span),
    )


def funcall(
    callee: Tagged[Expr],
    args: list[Tagged],
    call_start: int,
    call_end: int,
) -> Tagged[TransformedExpr]:
    call_span = S(call_start, call_end)
    return tag(
        TransformedExpr(operand=callee, transform=FunCallTransform(args=tag(args, call_span))),
        Span.covering(callee.span, call_span),
    )


def index_dot(lhs: Tagged[Expr], name: str, dot_offset: int) -> Tagged[TransformedExpr]:
    """a.name — op span = the dot, key span = the name (one char after the dot)."""
    key = lit(name, dot_offset + 1)
    return tag(
        TransformedExpr(
            operand=lhs, transform=BinOpTransform(op=tag(EagerOp.Index, S(dot_offset)), operand=key)
        ),
        Span.covering(lhs.span, key.span),
    )


def index_bracket(
    lhs: Tagged[Expr],
    key: Tagged[Expr],
    bracket_start: int,
    bracket_end: int,
) -> Tagged[TransformedExpr]:
    op_span = S(bracket_start, bracket_end)
    return tag(
        TransformedExpr(operand=lhs, transform=BinOpTransform(op=tag(EagerOp.Index, op_span), operand=key)),
        Span.covering(lhs.span, op_span),
    )


# shorthand binary ops
def add(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Add, op_start, op_end, rhs)  # noqa: E704


def sub(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Subtract, op_start, op_end, rhs)  # noqa: E704


def mul(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Multiply, op_start, op_end, rhs)  # noqa: E704


def div(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Divide, op_start, op_end, rhs)  # noqa: E704


def idiv(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.IntegerDivide, op_start, op_end, rhs)  # noqa: E704


def pow_(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Power, op_start, op_end, rhs)  # noqa: E704


def lt(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Less, op_start, op_end, rhs)  # noqa: E704


def gt(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Greater, op_start, op_end, rhs)  # noqa: E704


def lte(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.LessEqual, op_start, op_end, rhs)  # noqa: E704


def gte(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.GreaterEqual, op_start, op_end, rhs)  # noqa: E704


def eq(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.Equal, op_start, op_end, rhs)  # noqa: E704


def neq(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, EagerOp.NotEqual, op_start, op_end, rhs)  # noqa: E704


def and_(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, LogicOp.And, op_start, op_end, rhs)  # noqa: E704


def or_(
    lhs: Tagged[Expr],
    rhs: Tagged[Expr],
    op_start: int,
    op_end: int | None = None,
) -> Tagged[TransformedExpr]:
    return binop(lhs, LogicOp.Or, op_start, op_end, rhs)  # noqa: E704


# ── Test helpers ──────────────────────────────────────────────────────────────


def expr(source: str) -> Tagged[Expr]:
    result = parse(source)
    assert result.ok, f"Parse errors in {source!r}: {result.errors}"
    assert result.tree is not None
    return result.tree.expression


def first_error(source: str) -> Error:
    result = parse(source)
    assert result.errors, f"Expected parse error in {source!r}"
    return result.errors[0]


def err(source: str, offset: int) -> None:
    e = first_error(source)
    span = e.span
    assert span is not None
    assert span.offset == offset, (
        f"Expected error at offset {offset} in {source!r}, got {span.offset}: {e.message}"
    )


# ── Tests ─────────────────────────────────────────────────────────────────────


def test_booleans_and_null():
    assert expr("true") == lit(True, 0, 4)
    assert expr("false") == lit(False, 0, 5)
    assert expr("null") == lit(None, 0, 4)


def test_integers():
    assert expr("0") == lit(0, 0)
    assert expr("1") == lit(1, 0)
    assert expr("1  ") == lit(1, 0)
    assert expr("9223372036854775807") == lit(9223372036854775807, 0, 19)


def test_floats():
    assert expr("0.0") == lit(0.0, 0, 3)
    assert expr("0.") == lit(0.0, 0, 2)
    assert expr(".0") == lit(0.0, 0, 2)
    assert expr("0e0") == lit(0.0, 0, 3)
    assert expr("0e1") == lit(0.0, 0, 3)
    assert expr("1.") == lit(1.0, 0, 2)
    assert expr("1e+1") == lit(10.0, 0, 4)
    assert expr("1e1") == lit(10.0, 0, 3)
    assert expr("1e-1") == lit(0.1, 0, 4)


def test_strings():
    assert expr('""') == lit("", 0, 2)
    assert expr('"dingbob"') == lit("dingbob", 0, 9)
    assert expr('"ding\\"bob"') == lit('ding"bob', 0, 11)
    assert expr('"ding\\\\bob"') == lit("ding\\bob", 0, 11)

    assert expr('"dingbob${a}"') == tag(
        StringExpr(
            [
                StringRaw("dingbob"),
                StringInterpolate(expr=ident("a", 10), fmt=None),
            ]
        ),
        S(0, 13),
    )

    assert expr('"dingbob${ a}"') == tag(
        StringExpr(
            [
                StringRaw("dingbob"),
                StringInterpolate(expr=ident("a", 11), fmt=None),
            ]
        ),
        S(0, 14),
    )

    # Adjacent string parts are concatenated
    assert expr('"alpha" "bravo"') == tag(
        StringExpr([StringRaw("alpha"), StringRaw("bravo")]),
        S(0, 15),
    )


def test_string_format():
    assert expr('"${a}"') == tag(
        StringExpr([StringInterpolate(expr=ident("a", 3), fmt=None)]),
        S(0, 6),
    )

    assert expr('"${a:}"') == tag(
        StringExpr([StringInterpolate(expr=ident("a", 3), fmt=FormatSpec())]),
        S(0, 7),
    )

    assert expr('"${a: >+30}"') == tag(
        StringExpr(
            [
                StringInterpolate(
                    expr=ident("a", 3),
                    fmt=FormatSpec(align=AlignSpec.Right, sign=SignSpec.Plus, width=30),
                )
            ]
        ),
        S(0, 12),
    )

    assert expr('"${a:$^#.3}"') == tag(
        StringExpr(
            [
                StringInterpolate(
                    expr=ident("a", 3),
                    fmt=FormatSpec(fill="$", align=AlignSpec.Center, alternate=True, precision=3),
                )
            ]
        ),
        S(0, 12),
    )

    assert expr('"${a:0,.5s}"') == tag(
        StringExpr(
            [
                StringInterpolate(
                    expr=ident("a", 3),
                    fmt=FormatSpec(
                        fill="0",
                        align=AlignSpec.AfterSign,
                        grouping=GroupingSpec.Comma,
                        precision=5,
                        fmt_type=FormatTypeSpec.String,
                    ),
                )
            ]
        ),
        S(0, 12),
    )


def test_identifiers():
    assert expr("dingbob") == ident("dingbob", 0, 7)
    assert expr("lets") == ident("lets", 0, 4)
    assert expr("not1") == ident("not1", 0, 4)


def test_lists():
    assert expr("[]") == tag(ListExpr([]), S(0, 2))
    assert expr("[   ]") == tag(ListExpr([]), S(0, 5))

    assert expr("[true]") == tag(ListExpr([lel(True, 1, 5)]), S(0, 6))
    assert expr('[""]') == tag(ListExpr([lel("", 1, 3)]), S(0, 4))
    assert expr("[1,]") == tag(ListExpr([lel(1, 1)]), S(0, 4))
    assert expr("[  1   ,  ]") == tag(ListExpr([lel(1, 3)]), S(0, 11))

    assert expr("[  1   ,2  ]") == tag(ListExpr([lel(1, 3), lel(2, 8)]), S(0, 12))
    assert expr("[  1   ,2  ,]") == tag(ListExpr([lel(1, 3), lel(2, 8)]), S(0, 13))

    assert expr('[1, false, 2.3, "fable", lel]') == tag(
        ListExpr(
            [
                lel(1, 1),
                lel(False, 4, 9),
                lel(2.3, 11, 14),
                lel("fable", 16, 23),
                tag(ListSingleton(expr=ident("lel", 25, 28)), S(25, 28)),
            ]
        ),
        S(0, 29),
    )

    assert expr("[1, ...x, y]") == tag(
        ListExpr(
            [
                lel(1, 1),
                tag(ListSplat(expr=ident("x", 7)), S(4, 8)),
                tag(ListSingleton(expr=ident("y", 10)), S(10)),
            ]
        ),
        S(0, 12),
    )

    assert expr("[1, for x in y: x, 2]") == tag(
        ListExpr(
            [
                lel(1, 1),
                tag(
                    ListLoop(
                        binding=bid("x", 8),
                        iterable=ident("y", 13),
                        element=tag(ListSingleton(expr=ident("x", 16)), S(16)),
                    ),
                    S(4, 17),
                ),
                lel(2, 19),
            ]
        ),
        S(0, 21),
    )

    assert expr("[when f(x): x]") == tag(
        ListExpr(
            [
                tag(
                    ListCond(
                        condition=funcall(
                            ident("f", 6), [tag(ArgSingleton(expr=ident("x", 8)), S(8))], 7, 10
                        ),
                        element=tag(ListSingleton(expr=ident("x", 12)), S(12)),
                    ),
                    S(1, 13),
                ),
            ]
        ),
        S(0, 14),
    )

    assert expr("[ 1 , ... x , when x : y , for x in y : z , ]") == tag(
        ListExpr(
            [
                lel(1, 2),
                tag(ListSplat(expr=ident("x", 10)), S(6, 11)),
                tag(
                    ListCond(
                        condition=ident("x", 19),
                        element=tag(ListSingleton(expr=ident("y", 23)), S(23)),
                    ),
                    S(14, 24),
                ),
                tag(
                    ListLoop(
                        binding=bid("x", 31),
                        iterable=ident("y", 36),
                        element=tag(ListSingleton(expr=ident("z", 40)), S(40)),
                    ),
                    S(27, 41),
                ),
            ]
        ),
        S(0, 45),
    )

    assert expr("[ (1) , ... (x), when x: (y) , for x in y: (z) ]") == tag(
        ListExpr(
            [
                tag(ListSingleton(expr=lit(1, 3, 4)), S(3, 4)),
                tag(ListSplat(expr=ident("x", 13, 14)), S(8, 15)),
                tag(
                    ListCond(
                        condition=ident("x", 22),
                        element=tag(ListSingleton(expr=ident("y", 26, 27)), S(26, 27)),
                    ),
                    S(17, 28),
                ),
                tag(
                    ListLoop(
                        binding=bid("x", 35),
                        iterable=ident("y", 40),
                        element=tag(ListSingleton(expr=ident("z", 44, 45)), S(44, 45)),
                    ),
                    S(31, 46),
                ),
            ]
        ),
        S(0, 48),
    )


def test_nested_lists():
    assert expr("[[]]") == tag(
        ListExpr([tag(ListSingleton(expr=tag(ListExpr([]), S(1, 3))), S(1, 3))]),
        S(0, 4),
    )

    assert expr("[1, [2]]") == tag(
        ListExpr(
            [
                lel(1, 1),
                tag(ListSingleton(expr=tag(ListExpr([lel(2, 5)]), S(4, 7))), S(4, 7)),
            ]
        ),
        S(0, 8),
    )


def test_maps():
    assert expr("{}") == tag(MapExpr([]), S(0, 2))
    assert expr("{  }") == tag(MapExpr([]), S(0, 4))

    assert expr("{a: 1}") == tag(MapExpr([mel(lit("a", 1), lit(1, 4))]), S(0, 6))
    assert expr("{a: 1,}") == tag(MapExpr([mel(lit("a", 1), lit(1, 4))]), S(0, 7))
    assert expr("{  a :1,}") == tag(MapExpr([mel(lit("a", 3), lit(1, 6))]), S(0, 9))

    assert expr("{a: 1  ,b:2}") == tag(
        MapExpr([mel(lit("a", 1), lit(1, 4)), mel(lit("b", 8), lit(2, 10))]),
        S(0, 12),
    )

    assert expr("{che9: false}") == tag(
        MapExpr([mel(lit("che9", 1, 5), lit(False, 7, 12))]),
        S(0, 13),
    )

    assert expr('{fable: "fable"}') == tag(
        MapExpr([mel(lit("fable", 1, 6), lit("fable", 8, 15))]),
        S(0, 16),
    )

    assert expr("{format: 1}") == tag(
        MapExpr([mel(lit("format", 1, 7), lit(1, 9))]),
        S(0, 11),
    )

    assert expr('{a: 1, b: true, c: 2.e1, d: "hoho", e: 1e1}') == tag(
        MapExpr(
            [
                mel(lit("a", 1), lit(1, 4)),
                mel(lit("b", 7), lit(True, 10, 14)),
                mel(lit("c", 16), lit(20.0, 19, 23)),
                mel(lit("d", 25), lit("hoho", 28, 34)),
                mel(lit("e", 36), lit(10.0, 39, 42)),
            ]
        ),
        S(0, 43),
    )

    assert expr("{ident-with-hyphen: 1}") == tag(
        MapExpr([mel(lit("ident-with-hyphen", 1, 18), lit(1, 20))]),
        S(0, 22),
    )

    # $identifier key — key span is just the identifier (not the $)
    assert expr("{$z: y}") == tag(
        MapExpr([tag(MapSingleton(key=ident("z", 2), value=ident("y", 5)), S(1, 6))]),
        S(0, 7),
    )

    # $(expr) key — key span is the inner expression
    assert expr("{$(z): y}") == tag(
        MapExpr([tag(MapSingleton(key=ident("z", 3), value=ident("y", 7)), S(1, 8))]),
        S(0, 9),
    )

    assert expr('{"z": y}') == tag(
        MapExpr([mel(lit("z", 1, 4), ident("y", 6))]),
        S(0, 8),
    )

    # multiline string values
    src = "{\n   z:: here's some text\n}\n"
    assert expr(src) == tag(
        MapExpr(
            [
                mel(lit("z", 5).with_coord(1, 3), lit("here's some text", 8, 26).with_coord(1, 6)),
            ]
        ),
        S(0, 27),
    )

    assert expr("{...y, x: 1}") == tag(
        MapExpr(
            [
                tag(MapSplat(expr=ident("y", 4)), S(1, 5)),
                mel(lit("x", 7), lit(1, 10)),
            ]
        ),
        S(0, 12),
    )

    assert expr("{for [x,y] in z: x: y}") == tag(
        MapExpr(
            [
                tag(
                    MapLoop(
                        binding=tag(
                            ListPatternBinding(
                                binding=tag(
                                    ListBinding(
                                        [
                                            tag(
                                                ListBindingSingleton(binding=bid("x", 6), default=None), S(6)
                                            ),
                                            tag(
                                                ListBindingSingleton(binding=bid("y", 8), default=None), S(8)
                                            ),
                                        ]
                                    ),
                                    S(5, 10),
                                )
                            ),
                            S(5, 10),
                        ),
                        iterable=ident("z", 14),
                        element=mel(lit("x", 17), ident("y", 20)),
                    ),
                    S(1, 21),
                ),
            ]
        ),
        S(0, 22),
    )

    assert expr("{when f(x): z: y}") == tag(
        MapExpr(
            [
                tag(
                    MapCond(
                        condition=funcall(
                            ident("f", 6), [tag(ArgSingleton(expr=ident("x", 8)), S(8))], 7, 10
                        ),
                        element=mel(lit("z", 12), ident("y", 15)),
                    ),
                    S(1, 16),
                ),
            ]
        ),
        S(0, 17),
    )

    assert expr("{ a : 1 , ... x , when x : b : y , for x in y : c : z , $ f : 2 , }") == tag(
        MapExpr(
            [
                mel(lit("a", 2), lit(1, 6)),
                tag(MapSplat(expr=ident("x", 14)), S(10, 15)),
                tag(
                    MapCond(
                        condition=ident("x", 23),
                        element=mel(lit("b", 27), ident("y", 31)),
                    ),
                    S(18, 32),
                ),
                tag(
                    MapLoop(
                        binding=bid("x", 39),
                        iterable=ident("y", 44),
                        element=mel(lit("c", 48), ident("z", 52)),
                    ),
                    S(35, 53),
                ),
                tag(
                    MapSingleton(key=ident("f", 58), value=lit(2, 62)),
                    S(56, 63),
                ),
            ]
        ),
        S(0, 67),
    )


def test_let_blocks():
    assert expr('let a = "b" in 1') == tag(
        LetExpr(bindings=[(bid("a", 4), lit("b", 8, 11))], expression=lit(1, 15)),
        S(0, 16),
    )

    assert expr("let a = 1 let b = 2 in a") == tag(
        LetExpr(
            bindings=[(bid("a", 4), lit(1, 8)), (bid("b", 14), lit(2, 18))],
            expression=ident("a", 23),
        ),
        S(0, 24),
    )

    assert expr("let [a, b=1, ...] = c in [a, b]") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        ListPatternBinding(
                            binding=tag(
                                ListBinding(
                                    [
                                        tag(ListBindingSingleton(binding=bid("a", 5), default=None), S(5)),
                                        tag(
                                            ListBindingSingleton(binding=bid("b", 8), default=lit(1, 10)),
                                            S(8, 11),
                                        ),
                                        tag(ListBindingSlurp(), S(13, 16)),
                                    ]
                                ),
                                S(4, 17),
                            )
                        ),
                        S(4, 17),
                    ),
                    ident("c", 20),
                )
            ],
            expression=tag(
                ListExpr(
                    [
                        tag(ListSingleton(expr=ident("a", 26)), S(26)),
                        tag(ListSingleton(expr=ident("b", 29)), S(29)),
                    ]
                ),
                S(25, 31),
            ),
        ),
        S(0, 31),
    )

    assert expr("let [_, ...rest] = list in rest") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        ListPatternBinding(
                            binding=tag(
                                ListBinding(
                                    [
                                        tag(ListBindingSingleton(binding=bid("_", 5), default=None), S(5)),
                                        tag(ListBindingSlurpTo(name="rest"), S(8, 15)),
                                    ]
                                ),
                                S(4, 16),
                            )
                        ),
                        S(4, 16),
                    ),
                    ident("list", 19, 23),
                )
            ],
            expression=ident("rest", 27, 31),
        ),
        S(0, 31),
    )

    assert expr("let [...a] = b in a") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        ListPatternBinding(
                            binding=tag(
                                ListBinding([tag(ListBindingSlurpTo(name="a"), S(5, 9))]),
                                S(4, 10),
                            )
                        ),
                        S(4, 10),
                    ),
                    ident("b", 13),
                )
            ],
            expression=ident("a", 18),
        ),
        S(0, 19),
    )

    assert expr("let [...a,] = b in a") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        ListPatternBinding(
                            binding=tag(
                                ListBinding([tag(ListBindingSlurpTo(name="a"), S(5, 9))]),
                                S(4, 11),
                            )
                        ),
                        S(4, 11),
                    ),
                    ident("b", 14),
                )
            ],
            expression=ident("a", 19),
        ),
        S(0, 20),
    )

    assert expr("let {a} = x in a") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        MapPatternBinding(
                            binding=tag(
                                MapBinding(
                                    [
                                        tag(
                                            MapBindingSingleton(
                                                key=tag("a", S(5)),
                                                binding=tag(IdentifierBinding(name=tag("a", S(5))), S(5)),
                                                default=None,
                                            ),
                                            S(5),
                                        ),
                                    ]
                                ),
                                S(4, 7),
                            )
                        ),
                        S(4, 7),
                    ),
                    ident("x", 10),
                )
            ],
            expression=ident("a", 15),
        ),
        S(0, 16),
    )

    assert expr("let {a as b} = x in a") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        MapPatternBinding(
                            binding=tag(
                                MapBinding(
                                    [
                                        tag(
                                            MapBindingSingleton(
                                                key=tag("a", S(5)),
                                                binding=bid("b", 10),
                                                default=None,
                                            ),
                                            S(5, 11),
                                        ),
                                    ]
                                ),
                                S(4, 12),
                            )
                        ),
                        S(4, 12),
                    ),
                    ident("x", 15),
                )
            ],
            expression=ident("a", 20),
        ),
        S(0, 21),
    )

    assert expr("let {a = y} = x in a") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        MapPatternBinding(
                            binding=tag(
                                MapBinding(
                                    [
                                        tag(
                                            MapBindingSingleton(
                                                key=tag("a", S(5)),
                                                binding=tag(IdentifierBinding(name=tag("a", S(5))), S(5)),
                                                default=ident("y", 9),
                                            ),
                                            S(5, 10),
                                        ),
                                    ]
                                ),
                                S(4, 11),
                            )
                        ),
                        S(4, 11),
                    ),
                    ident("x", 14),
                )
            ],
            expression=ident("a", 19),
        ),
        S(0, 20),
    )

    assert expr("let {a as b = y} = x in a") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        MapPatternBinding(
                            binding=tag(
                                MapBinding(
                                    [
                                        tag(
                                            MapBindingSingleton(
                                                key=tag("a", S(5)),
                                                binding=bid("b", 10),
                                                default=ident("y", 14),
                                            ),
                                            S(5, 15),
                                        ),
                                    ]
                                ),
                                S(4, 16),
                            )
                        ),
                        S(4, 16),
                    ),
                    ident("x", 19),
                )
            ],
            expression=ident("a", 24),
        ),
        S(0, 25),
    )

    assert expr("let [ y = (1) ] = x in y") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        ListPatternBinding(
                            binding=tag(
                                ListBinding(
                                    [
                                        tag(
                                            ListBindingSingleton(binding=bid("y", 6), default=lit(1, 11, 12)),
                                            S(6, 13),
                                        ),
                                    ]
                                ),
                                S(4, 15),
                            )
                        ),
                        S(4, 15),
                    ),
                    ident("x", 18),
                )
            ],
            expression=ident("y", 23),
        ),
        S(0, 24),
    )

    assert expr("let { y = (1) } = x in y") == tag(
        LetExpr(
            bindings=[
                (
                    tag(
                        MapPatternBinding(
                            binding=tag(
                                MapBinding(
                                    [
                                        tag(
                                            MapBindingSingleton(
                                                key=tag("y", S(6)),
                                                binding=tag(IdentifierBinding(name=tag("y", S(6))), S(6)),
                                                default=lit(1, 11, 12),
                                            ),
                                            S(6, 13),
                                        ),
                                    ]
                                ),
                                S(4, 15),
                            )
                        ),
                        S(4, 15),
                    ),
                    ident("x", 18),
                )
            ],
            expression=ident("y", 23),
        ),
        S(0, 24),
    )


def test_branching():
    assert expr("if a then b else c") == tag(
        BranchExpr(
            condition=ident("a", 3),
            true_branch=ident("b", 10),
            false_branch=ident("c", 17),
        ),
        S(0, 18),
    )


def test_indexing():
    assert expr("a.b") == index_dot(ident("a", 0), "b", 1)
    assert expr("a[b]") == index_bracket(ident("a", 0), ident("b", 2), 1, 4)

    assert expr("a.b.c") == index_dot(index_dot(ident("a", 0), "b", 1), "c", 3)

    assert expr("a[b].c") == index_dot(
        index_bracket(ident("a", 0), ident("b", 2), 1, 4),
        "c",
        4,
    )

    assert expr("a.b[c]") == index_bracket(
        index_dot(ident("a", 0), "b", 1),
        ident("c", 4),
        3,
        6,
    )

    assert expr("a[b][c]") == index_bracket(
        index_bracket(ident("a", 0), ident("b", 2), 1, 4),
        ident("c", 5),
        4,
        7,
    )


def test_funcall():
    assert expr("func(1, 2, 3,)") == funcall(
        ident("func", 0, 4),
        [
            tag(ArgSingleton(expr=lit(1, 5)), S(5)),
            tag(ArgSingleton(expr=lit(2, 8)), S(8)),
            tag(ArgSingleton(expr=lit(3, 11)), S(11)),
        ],
        4,
        14,
    )

    assert expr("func(1, 2, a: 3)") == funcall(
        ident("func", 0, 4),
        [
            tag(ArgSingleton(expr=lit(1, 5)), S(5)),
            tag(ArgSingleton(expr=lit(2, 8)), S(8)),
            tag(ArgKeyword(key=tag("a", S(11)), expr=lit(3, 14)), S(11, 15)),
        ],
        4,
        16,
    )

    assert expr("func(a: 2, b: 3)") == funcall(
        ident("func", 0, 4),
        [
            tag(ArgKeyword(key=tag("a", S(5)), expr=lit(2, 8)), S(5, 9)),
            tag(ArgKeyword(key=tag("b", S(11)), expr=lit(3, 14)), S(11, 15)),
        ],
        4,
        16,
    )

    # Immediately invoked function
    assert expr("(fn (x,y) x+y)(1,2)") == retag(
        funcall(
            tag(
                FunctionExpr(
                    positional=tag(
                        ListBinding(
                            [
                                tag(ListBindingSingleton(binding=bid("x", 5), default=None), S(5)),
                                tag(ListBindingSingleton(binding=bid("y", 7), default=None), S(7)),
                            ]
                        ),
                        S(4, 9),
                    ),
                    keywords=None,
                    expression=add(ident("x", 10), ident("y", 12), 11),
                ),
                S(1, 13),  # inner span of fn expr (without surrounding parens)
            ),
            [
                tag(ArgSingleton(expr=lit(1, 15)), S(15)),
                tag(ArgSingleton(expr=lit(2, 17)), S(17)),
            ],
            14,
            19,
        ),
        0,
        19,
    )

    assert expr("func(1, ...y, z: 2, ...q)") == funcall(
        ident("func", 0, 4),
        [
            tag(ArgSingleton(expr=lit(1, 5)), S(5)),
            tag(ArgSplat(expr=ident("y", 11)), S(8, 12)),
            tag(ArgKeyword(key=tag("z", S(14)), expr=lit(2, 17)), S(14, 18)),
            tag(ArgSplat(expr=ident("q", 23)), S(20, 24)),
        ],
        4,
        25,
    )


def test_unary_operators():
    assert expr("-1") == unop(lit(1, 1), UnOp.ArithmeticalNegate, 0)
    assert expr("- not 1") == unop(unop(lit(1, 6), UnOp.LogicalNegate, 2, 5), UnOp.ArithmeticalNegate, 0)
    assert expr("not -1") == unop(unop(lit(1, 5), UnOp.ArithmeticalNegate, 4), UnOp.LogicalNegate, 0, 3)


def test_power_operators():
    assert expr("2^3") == pow_(lit(2, 0), lit(3, 2), 1)
    assert expr("2^-3") == pow_(lit(2, 0), unop(lit(3, 3), UnOp.ArithmeticalNegate, 2), 1)
    assert expr("-2^3") == unop(pow_(lit(2, 1), lit(3, 3), 2), UnOp.ArithmeticalNegate, 0)
    assert expr("-2^-3") == unop(
        pow_(lit(2, 1), unop(lit(3, 4), UnOp.ArithmeticalNegate, 3), 2, 3),
        UnOp.ArithmeticalNegate,
        0,
    )


def test_operators():
    assert expr("1 + 2") == add(lit(1, 0), lit(2, 4), 2)

    assert expr("1 / 2 + 3") == add(
        div(lit(1, 0), lit(2, 4), 2),
        lit(3, 8),
        6,
    )

    assert expr("1 + 2 - 3 * 4 // 5 / 6") == sub(
        add(lit(1, 0), lit(2, 4), 2),
        div(
            idiv(mul(lit(3, 8), lit(4, 12), 10), lit(5, 17), 14, 16),
            lit(6, 21),
            19,
        ),
        6,
    )

    assert expr("1 < 2") == lt(lit(1, 0), lit(2, 4), 2)

    assert expr("1 > 2 <= 3 >= 4 == 5 != 6") == neq(
        eq(
            gte(lte(gt(lit(1, 0), lit(2, 4), 2), lit(3, 9), 6, 8), lit(4, 14), 11, 13),
            lit(5, 19),
            16,
            18,
        ),
        lit(6, 24),
        21,
        23,
    )

    assert expr("1 and 2 or 3") == or_(
        and_(lit(1, 0), lit(2, 6), 2, 5),
        lit(3, 11),
        8,
        10,
    )

    assert expr("2 // 2 * 2") == mul(
        idiv(lit(2, 0), lit(2, 5), 2, 4),
        lit(2, 9),
        7,
        8,
    )

    assert expr("2 ^ 2 ^ 2") == pow_(lit(2, 0), pow_(lit(2, 4), lit(2, 8), 6), 2)

    assert expr("-2 ^ 2 ^ 2") == unop(
        pow_(lit(2, 1), pow_(lit(2, 5), lit(2, 9), 7), 3),
        UnOp.ArithmeticalNegate,
        0,
    )

    assert expr("(1 + 2) * 5") == retag(mul(add(lit(1, 1), lit(2, 5), 3), lit(5, 10), 8), 0, 11)


def test_functions():
    assert expr("fn () 1") == tag(
        FunctionExpr(
            positional=tag(ListBinding([]), S(3, 5)),
            keywords=None,
            expression=lit(1, 6),
        ),
        S(0, 7),
    )

    assert expr("fn (;) 1") == tag(
        FunctionExpr(
            positional=tag(ListBinding([]), S(3, 5)),
            keywords=tag(MapBinding([]), S(4, 6)),
            expression=lit(1, 7),
        ),
        S(0, 8),
    )

    assert expr("fn {} 1") == tag(
        FunctionExpr(
            positional=tag(ListBinding([]), S(3)),
            keywords=tag(MapBinding([]), S(3, 5)),
            expression=lit(1, 6),
        ),
        S(0, 7),
    )

    assert expr("fn (a) let b = a in b") == tag(
        FunctionExpr(
            positional=tag(
                ListBinding([tag(ListBindingSingleton(binding=bid("a", 4), default=None), S(4))]), S(3, 6)
            ),
            keywords=None,
            expression=tag(
                LetExpr(
                    bindings=[(bid("b", 11), ident("a", 15))],
                    expression=ident("b", 20),
                ),
                S(7, 21),
            ),
        ),
        S(0, 21),
    )

    assert expr("fn {x=1, y=2} x + y") == tag(
        FunctionExpr(
            positional=tag(ListBinding([]), S(3)),
            keywords=tag(
                MapBinding(
                    [
                        tag(
                            MapBindingSingleton(
                                key=tag("x", S(4)),
                                binding=tag(IdentifierBinding(name=tag("x", S(4))), S(4)),
                                default=lit(1, 6),
                            ),
                            S(4, 7),
                        ),
                        tag(
                            MapBindingSingleton(
                                key=tag("y", S(9)),
                                binding=tag(IdentifierBinding(name=tag("y", S(9))), S(9)),
                                default=lit(2, 11),
                            ),
                            S(9, 12),
                        ),
                    ]
                ),
                S(3, 13),
            ),
            expression=add(ident("x", 14), ident("y", 18), 16),
        ),
        S(0, 19),
    )


def test_errors():
    # let
    err("let", 3)
    err("let a", 5)
    err("let a =", 7)
    err("let a = 1", 9)
    err("let a = 1 in", 12)

    # if
    err("if", 2)
    err("if true", 7)
    err("if true then", 12)
    err("if true then 1", 14)
    err("if true then 1 else", 19)

    # list
    err("[", 1)
    err("[1", 2)
    err("[1,", 3)
    err("[...", 4)
    err("[when", 5)
    err("[when x", 7)
    err("[when x:", 8)
    err("[when x: 1", 10)
    err("[for", 4)
    err("[for x", 6)
    err("[for x in", 9)
    err("[for x in y", 11)
    err("[for x in y:", 12)
    err("[for x in y: z", 14)

    # map
    err("{", 1)
    err("{x", 2)
    err("{x:", 3)
    err("{x: y", 5)
    err("{x: y,", 6)
    err("{$", 2)
    err("{$x", 3)
    err("{$x:", 4)
    err("{$x: y", 6)
    err("{$x: y,", 7)
    err("{...", 4)
    err("{when", 5)
    err("{when x", 7)
    err("{when x:", 8)
    err("{when x: y", 10)
    err("{when x: y:", 11)
    err("{when x: y: 1", 13)
    err("{for", 4)
    err("{for x", 6)
    err("{for x in", 9)
    err("{for x in y", 11)
    err("{for x in y:", 12)
    err("{for x in y: z", 14)
    err("{for x in y: z:", 15)
    err("{for x in y: z: v", 17)

    # let bindings
    err("let [", 5)
    err("let [x", 6)
    err("let [x,", 7)
    err("let [x =", 8)
    err("let [x = 1", 10)
    err("let [...", 8)
    err("let {", 5)
    err("let {y", 6)
    err("let {y,", 7)
    err("let {y =", 8)
    err("let {y = 1", 10)
    err("let {y as", 9)
    err("let {y as x =", 13)
    err("let {...", 8)
    err("let {...x", 9)

    # parens
    err("(", 1)
    err("(1", 2)

    # fn
    err("fn (", 4)
    err("fn (x", 5)
    err("fn (x,", 6)
    err("fn (;", 5)
    err("fn (;y", 6)
    err("fn (;y,", 7)
    err("fn ()", 5)
    err("fn {", 4)
    err("fn {x", 5)
    err("fn {x,", 6)
    err("fn {}", 5)

    # strings
    err('"alpha', 6)
    err('"alpha$', 7)
    err('"alpha${', 8)
    err('"alpha${1', 9)
    err('"alpha${1}', 10)

    # postfix
    err("a.", 2)
    err("a[", 2)
    err("a[1", 3)
    err("a(", 2)
    err("a(1", 3)
    err("a(1,", 4)
    err("a(x:", 4)
    err("a(...", 5)

    # operators
    err("-", 1)
    err("1+", 2)

    # import
    err("import", 6)
    err('import "path"', 13)
    err('import "path" as', 16)
    err('import "path" as y', 18)


# ── Multiline string additional tests ─────────────────────────────────────────


def _multistring_val(src: str) -> GoldValue:
    result = parse(src)
    assert result.ok
    assert result.tree is not None
    mp = result.tree.expression.contents
    assert isinstance(mp, MapExpr)
    elem = mp.elements[0].contents
    assert isinstance(elem, MapSingleton)
    val = elem.value.contents
    assert isinstance(val, LiteralExpr)
    return val.value


def test_multiline_strings():
    assert _multistring_val("{\n   z:: here's some\n    text\n}\n") == "here's some\ntext"
    assert _multistring_val("{\n   z:: here's some\n     text\n}\n") == "here's some\ntext"

    # deeper indent → extra leading spaces on each extra line
    assert _multistring_val("{\n   z::\n     here's some\n       text\n}\n") == "here's some\n  text"

    # shallower indent → text stripped to common indent
    assert _multistring_val("{\n   z::\n       here's some\n     text\n}\n") == "  here's some\ntext"
