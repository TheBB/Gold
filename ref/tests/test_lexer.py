from __future__ import annotations

import pytest

from ref.error import Error
from ref.lexer import Lexer, Token, TokenType
from ref.span import Span, Tagged, tag

# ── Helpers ───────────────────────────────────────────────────────────────────


def tok(result: tuple[Lexer, Tagged[Token]], expected: Tagged[Token]) -> Lexer:
    lex, actual = result
    assert actual == expected
    return lex


def stop(lex: Lexer) -> None:
    with pytest.raises(Error):
        lex.next_token()


def t(token: Token, start: int, end: int | None = None) -> Tagged[Token]:
    if end is None:
        return tag(token, Span.from_offset(start))
    return tag(token, Span.from_offsets(start, end))


def name(s: str) -> Token:
    return Token(TokenType.Name, s)


def float_(s: str) -> Token:
    return Token(TokenType.Float, s)


def int_(s: str) -> Token:
    return Token(TokenType.Integer, s)


def stringlit(s: str) -> Token:
    return Token(TokenType.StringLit, s)


def multistring(s: str) -> Token:
    return Token(TokenType.MultiString, s)


def dquote() -> Token:
    return Token(TokenType.DoubleQuote, '"')


def dollar() -> Token:
    return Token(TokenType.Dollar, "$")


def comma() -> Token:
    return Token(TokenType.Comma, ",")


def colon() -> Token:
    return Token(TokenType.Colon, ":")


def dcolon() -> Token:
    return Token(TokenType.DoubleColon, "::")


def ellipsis() -> Token:
    return Token(TokenType.Ellipsis, "...")


def openbrace() -> Token:
    return Token(TokenType.OpenBrace, "{")


def closebrace() -> Token:
    return Token(TokenType.CloseBrace, "}")


def openbracket() -> Token:
    return Token(TokenType.OpenBracket, "[")


def closebracket() -> Token:
    return Token(TokenType.CloseBracket, "]")


def openparen() -> Token:
    return Token(TokenType.OpenParen, "(")


def closeparen() -> Token:
    return Token(TokenType.CloseParen, ")")


# ── Tests ─────────────────────────────────────────────────────────────────────


def test_whitespace() -> None:
    lex = Lexer.new("dingbob")
    lex = tok(lex.next_token(), t(name("dingbob"), 0, 7))
    stop(lex)

    lex = Lexer.new("\ndingbob")
    lex = tok(lex.next_token(), t(name("dingbob"), 1, 8).with_coord(1, 0))
    stop(lex)

    lex = Lexer.new("# this is a comment\ndingbob")
    lex = tok(lex.next_token(), t(name("dingbob"), 20, 27).with_coord(1, 0))
    stop(lex)

    lex = Lexer.new("dingbob\n#this is a comment")
    lex = tok(lex.next_token(), t(name("dingbob"), 0, 7))
    stop(lex)

    lex = Lexer.new("dingbob#this is a comment")
    lex = tok(lex.next_token(), t(name("dingbob"), 0, 7))
    stop(lex)

    lex = Lexer.new("# this is a comment\n#a\n#b\ndingbob")
    lex = tok(lex.next_token(), t(name("dingbob"), 26, 33).with_coord(3, 0))
    stop(lex)


def test_booleans_and_null() -> None:
    lex = Lexer.new("true")
    lex = tok(lex.next_token(), t(name("true"), 0, 4))
    stop(lex)

    lex = Lexer.new("false")
    lex = tok(lex.next_token(), t(name("false"), 0, 5))
    stop(lex)

    lex = Lexer.new("null")
    lex = tok(lex.next_token(), t(name("null"), 0, 4))
    stop(lex)


def test_floats() -> None:
    lex = Lexer.new("0.0")
    lex = tok(lex.next_token(), t(float_("0.0"), 0, 3))
    stop(lex)

    lex = Lexer.new("0.")
    lex = tok(lex.next_token(), t(float_("0."), 0, 2))
    stop(lex)

    lex = Lexer.new(".0")
    lex = tok(lex.next_token(), t(float_(".0"), 0, 2))
    stop(lex)

    lex = Lexer.new("0e0")
    lex = tok(lex.next_token(), t(float_("0e0"), 0, 3))
    stop(lex)

    lex = Lexer.new("0e1")
    lex = tok(lex.next_token(), t(float_("0e1"), 0, 3))
    stop(lex)

    lex = Lexer.new("1.")
    lex = tok(lex.next_token(), t(float_("1."), 0, 2))
    stop(lex)

    lex = Lexer.new("1e+1")
    lex = tok(lex.next_token(), t(float_("1e+1"), 0, 4))
    stop(lex)

    lex = Lexer.new("1e1")
    lex = tok(lex.next_token(), t(float_("1e1"), 0, 3))
    stop(lex)

    lex = Lexer.new("1e-1")
    lex = tok(lex.next_token(), t(float_("1e-1"), 0, 4))
    stop(lex)


def test_strings() -> None:
    lex = Lexer.new('""')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(dquote(), 1))
    stop(lex)

    lex = Lexer.new('"dingbob"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("dingbob"), 1, 8))
    lex = tok(lex.next_string(), t(dquote(), 8))
    stop(lex)

    lex = Lexer.new(r'"ding\"bob"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit(r"ding\"bob"), 1, 10))
    lex = tok(lex.next_string(), t(dquote(), 10))
    stop(lex)

    lex = Lexer.new(r'"ding\\bob"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit(r"ding\\bob"), 1, 10))
    lex = tok(lex.next_string(), t(dquote(), 10))
    stop(lex)

    lex = Lexer.new('"dingbob$')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("dingbob"), 1, 8))
    lex = tok(lex.next_string(), t(dollar(), 8))
    stop(lex)

    lex = Lexer.new('"dingbob$do')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("dingbob"), 1, 8))
    lex = tok(lex.next_string(), t(dollar(), 8))
    lex = tok(lex.next_token(), t(name("do"), 9, 11))
    stop(lex)

    lex = Lexer.new('"a + b = $a + $b"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("a + b = "), 1, 9))
    lex = tok(lex.next_string(), t(dollar(), 9))
    lex = tok(lex.next_token(), t(name("a"), 10))
    lex = tok(lex.next_string(), t(stringlit(" + "), 11, 14))
    lex = tok(lex.next_string(), t(dollar(), 14))
    lex = tok(lex.next_token(), t(name("b"), 15))
    lex = tok(lex.next_token(), t(dquote(), 16))
    stop(lex)

    lex = Lexer.new('"a + b = $a + $b = ${sum}"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("a + b = "), 1, 9))
    lex = tok(lex.next_string(), t(dollar(), 9))
    lex = tok(lex.next_token(), t(name("a"), 10))
    lex = tok(lex.next_string(), t(stringlit(" + "), 11, 14))
    lex = tok(lex.next_string(), t(dollar(), 14))
    lex = tok(lex.next_token(), t(name("b"), 15))
    lex = tok(lex.next_string(), t(stringlit(" = "), 16, 19))
    lex = tok(lex.next_string(), t(dollar(), 19))
    lex = tok(lex.next_token(), t(openbrace(), 20))
    lex = tok(lex.next_token(), t(name("sum"), 21, 24))
    lex = tok(lex.next_token(), t(closebrace(), 24))
    lex = tok(lex.next_string(), t(dquote(), 25))
    stop(lex)

    lex = Lexer.new('"dingbob${a}"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("dingbob"), 1, 8))
    lex = tok(lex.next_string(), t(dollar(), 8))
    lex = tok(lex.next_token(), t(openbrace(), 9))
    lex = tok(lex.next_token(), t(name("a"), 10))
    lex = tok(lex.next_token(), t(closebrace(), 11))
    lex = tok(lex.next_string(), t(dquote(), 12))
    stop(lex)

    lex = Lexer.new('"dingbob${ a}"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("dingbob"), 1, 8))
    lex = tok(lex.next_string(), t(dollar(), 8))
    lex = tok(lex.next_token(), t(openbrace(), 9))
    lex = tok(lex.next_token(), t(name("a"), 11))
    lex = tok(lex.next_token(), t(closebrace(), 12))
    lex = tok(lex.next_string(), t(dquote(), 13))
    stop(lex)

    lex = Lexer.new('"alpha" "bravo"')
    lex = tok(lex.next_token(), t(dquote(), 0))
    lex = tok(lex.next_string(), t(stringlit("alpha"), 1, 6))
    lex = tok(lex.next_string(), t(dquote(), 6))
    lex = tok(lex.next_token(), t(dquote(), 8))
    lex = tok(lex.next_string(), t(stringlit("bravo"), 9, 14))
    lex = tok(lex.next_string(), t(dquote(), 14))
    stop(lex)


def test_identifiers() -> None:
    lex = Lexer.new("dingbob")
    lex = tok(lex.next_token(), t(name("dingbob"), 0, 7))
    stop(lex)

    lex = Lexer.new("lets")
    lex = tok(lex.next_token(), t(name("lets"), 0, 4))
    stop(lex)

    lex = Lexer.new("not1")
    lex = tok(lex.next_token(), t(name("not1"), 0, 4))
    stop(lex)

    lex = Lexer.new("null1")
    lex = tok(lex.next_token(), t(name("null1"), 0, 5))
    stop(lex)


def test_lists() -> None:
    lex = Lexer.new("[]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(closebracket(), 1))
    stop(lex)

    lex = Lexer.new("[   ]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(closebracket(), 4))
    stop(lex)

    lex = Lexer.new("[true]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(name("true"), 1, 5))
    lex = tok(lex.next_token(), t(closebracket(), 5))
    stop(lex)

    lex = Lexer.new('[""]')
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(dquote(), 1))
    lex = tok(lex.next_string(), t(dquote(), 2))
    lex = tok(lex.next_token(), t(closebracket(), 3))
    stop(lex)

    lex = Lexer.new("[1,]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(int_("1"), 1))
    lex = tok(lex.next_token(), t(comma(), 2))
    lex = tok(lex.next_token(), t(closebracket(), 3))
    stop(lex)

    lex = Lexer.new('[1, false, 2.3, "fable", lel]')
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(int_("1"), 1))
    lex = tok(lex.next_token(), t(comma(), 2))
    lex = tok(lex.next_token(), t(name("false"), 4, 9))
    lex = tok(lex.next_token(), t(comma(), 9))
    lex = tok(lex.next_token(), t(float_("2.3"), 11, 14))
    lex = tok(lex.next_token(), t(comma(), 14))
    lex = tok(lex.next_token(), t(dquote(), 16))
    lex = tok(lex.next_string(), t(stringlit("fable"), 17, 22))
    lex = tok(lex.next_string(), t(dquote(), 22))
    lex = tok(lex.next_token(), t(comma(), 23))
    lex = tok(lex.next_token(), t(name("lel"), 25, 28))
    lex = tok(lex.next_token(), t(closebracket(), 28))
    stop(lex)

    lex = Lexer.new("[1, ...x, y]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(int_("1"), 1))
    lex = tok(lex.next_token(), t(comma(), 2))
    lex = tok(lex.next_token(), t(ellipsis(), 4, 7))
    lex = tok(lex.next_token(), t(name("x"), 7))
    lex = tok(lex.next_token(), t(comma(), 8))
    lex = tok(lex.next_token(), t(name("y"), 10))
    lex = tok(lex.next_token(), t(closebracket(), 11))
    stop(lex)

    lex = Lexer.new("[1, for x in y: x, 2]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(int_("1"), 1))
    lex = tok(lex.next_token(), t(comma(), 2))
    lex = tok(lex.next_token(), t(name("for"), 4, 7))
    lex = tok(lex.next_token(), t(name("x"), 8))
    lex = tok(lex.next_token(), t(name("in"), 10, 12))
    lex = tok(lex.next_token(), t(name("y"), 13))
    lex = tok(lex.next_token(), t(colon(), 14))
    lex = tok(lex.next_token(), t(name("x"), 16))
    lex = tok(lex.next_token(), t(comma(), 17))
    lex = tok(lex.next_token(), t(int_("2"), 19))
    lex = tok(lex.next_token(), t(closebracket(), 20))
    stop(lex)

    lex = Lexer.new("[when f(x): x]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(name("when"), 1, 5))
    lex = tok(lex.next_token(), t(name("f"), 6))
    lex = tok(lex.next_token(), t(openparen(), 7))
    lex = tok(lex.next_token(), t(name("x"), 8))
    lex = tok(lex.next_token(), t(closeparen(), 9))
    lex = tok(lex.next_token(), t(colon(), 10))
    lex = tok(lex.next_token(), t(name("x"), 12))
    lex = tok(lex.next_token(), t(closebracket(), 13))
    stop(lex)

    lex = Lexer.new("[[]]")
    lex = tok(lex.next_token(), t(openbracket(), 0))
    lex = tok(lex.next_token(), t(openbracket(), 1))
    lex = tok(lex.next_token(), t(closebracket(), 2))
    lex = tok(lex.next_token(), t(closebracket(), 3))
    stop(lex)


def test_maps() -> None:
    lex = Lexer.new("{}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(closebrace(), 1))
    stop(lex)

    lex = Lexer.new("{  }")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(closebrace(), 3))
    stop(lex)

    lex = Lexer.new("{a: 1}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("a"), 1))
    lex = tok(lex.next_token(), t(colon(), 2))
    lex = tok(lex.next_token(), t(int_("1"), 4))
    lex = tok(lex.next_token(), t(closebrace(), 5))
    stop(lex)

    lex = Lexer.new("{a: 1,}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("a"), 1))
    lex = tok(lex.next_token(), t(colon(), 2))
    lex = tok(lex.next_token(), t(int_("1"), 4))
    lex = tok(lex.next_token(), t(comma(), 5))
    lex = tok(lex.next_token(), t(closebrace(), 6))
    stop(lex)

    lex = Lexer.new("{che9: false}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("che9"), 1, 5))
    lex = tok(lex.next_token(), t(colon(), 5))
    lex = tok(lex.next_token(), t(name("false"), 7, 12))
    lex = tok(lex.next_token(), t(closebrace(), 12))
    stop(lex)

    lex = Lexer.new('{fable: "fable"}')
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("fable"), 1, 6))
    lex = tok(lex.next_token(), t(colon(), 6))
    lex = tok(lex.next_token(), t(dquote(), 8))
    lex = tok(lex.next_string(), t(stringlit("fable"), 9, 14))
    lex = tok(lex.next_string(), t(dquote(), 14))
    lex = tok(lex.next_token(), t(closebrace(), 15))
    stop(lex)

    lex = Lexer.new('{a: 1, b: true, c: 2.e1, d: "hoho", e: 1e1}')
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("a"), 1))
    lex = tok(lex.next_token(), t(colon(), 2))
    lex = tok(lex.next_token(), t(int_("1"), 4))
    lex = tok(lex.next_token(), t(comma(), 5))
    lex = tok(lex.next_key(), t(name("b"), 7))
    lex = tok(lex.next_token(), t(colon(), 8))
    lex = tok(lex.next_token(), t(name("true"), 10, 14))
    lex = tok(lex.next_token(), t(comma(), 14))
    lex = tok(lex.next_key(), t(name("c"), 16))
    lex = tok(lex.next_token(), t(colon(), 17))
    lex = tok(lex.next_token(), t(float_("2.e1"), 19, 23))
    lex = tok(lex.next_token(), t(comma(), 23))
    lex = tok(lex.next_key(), t(name("d"), 25))
    lex = tok(lex.next_token(), t(colon(), 26))
    lex = tok(lex.next_token(), t(dquote(), 28))
    lex = tok(lex.next_string(), t(stringlit("hoho"), 29, 33))
    lex = tok(lex.next_string(), t(dquote(), 33))
    lex = tok(lex.next_token(), t(comma(), 34))
    lex = tok(lex.next_key(), t(name("e"), 36))
    lex = tok(lex.next_token(), t(colon(), 37))
    lex = tok(lex.next_token(), t(float_("1e1"), 39, 42))
    lex = tok(lex.next_token(), t(closebrace(), 42))
    stop(lex)

    lex = Lexer.new("{ident-with-hyphen: 1}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("ident-with-hyphen"), 1, 18))
    lex = tok(lex.next_token(), t(colon(), 18))
    lex = tok(lex.next_token(), t(int_("1"), 20))
    lex = tok(lex.next_token(), t(closebrace(), 21))
    stop(lex)

    lex = Lexer.new("{$z: y}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(dollar(), 1))
    lex = tok(lex.next_token(), t(name("z"), 2))
    lex = tok(lex.next_token(), t(colon(), 3))
    lex = tok(lex.next_token(), t(name("y"), 5))
    lex = tok(lex.next_token(), t(closebrace(), 6))
    stop(lex)

    lex = Lexer.new('{$"z": y}')
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(dollar(), 1))
    lex = tok(lex.next_token(), t(dquote(), 2))
    lex = tok(lex.next_string(), t(stringlit("z"), 3))
    lex = tok(lex.next_string(), t(dquote(), 4))
    lex = tok(lex.next_token(), t(colon(), 5))
    lex = tok(lex.next_token(), t(name("y"), 7))
    lex = tok(lex.next_token(), t(closebrace(), 8))
    stop(lex)

    lex = Lexer.new("{\n   z:: here's some text\n}\n")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("z"), 5).with_coord(1, 3))
    lex = tok(lex.next_token(), t(dcolon(), 6, 8).with_coord(1, 4))
    lex = tok(lex.next_multistring(3), t(multistring(" here's some text\n"), 8, 26).with_coord(1, 6))
    lex = tok(lex.next_token(), t(closebrace(), 26).with_coord(2, 0))
    stop(lex)

    lex = Lexer.new("{\n   z:: here's some\n       text\n}\n")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("z"), 5).with_coord(1, 3))
    lex = tok(lex.next_token(), t(dcolon(), 6, 8).with_coord(1, 4))
    lex = tok(
        lex.next_multistring(3),
        t(multistring(" here's some\n       text\n"), 8, 33).with_coord(1, 6),
    )
    lex = tok(lex.next_token(), t(closebrace(), 33).with_coord(3, 0))
    stop(lex)

    lex = Lexer.new("{\n   z:: here's some\n     text\n}\n")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("z"), 5).with_coord(1, 3))
    lex = tok(lex.next_token(), t(dcolon(), 6, 8).with_coord(1, 4))
    lex = tok(
        lex.next_multistring(3),
        t(multistring(" here's some\n     text\n"), 8, 31).with_coord(1, 6),
    )
    lex = tok(lex.next_token(), t(closebrace(), 31).with_coord(3, 0))
    stop(lex)

    lex = Lexer.new("{\n   z::\n     here's some\n     text\n}\n")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("z"), 5).with_coord(1, 3))
    lex = tok(lex.next_token(), t(dcolon(), 6, 8).with_coord(1, 4))
    lex = tok(
        lex.next_multistring(3),
        t(multistring("\n     here's some\n     text\n"), 8, 36).with_coord(1, 6),
    )
    lex = tok(lex.next_token(), t(closebrace(), 36).with_coord(4, 0))
    stop(lex)

    lex = Lexer.new("{\n   z::\n     here's some\n       text\n}\n")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("z"), 5).with_coord(1, 3))
    lex = tok(lex.next_token(), t(dcolon(), 6, 8).with_coord(1, 4))
    lex = tok(
        lex.next_multistring(3),
        t(multistring("\n     here's some\n       text\n"), 8, 38).with_coord(1, 6),
    )
    lex = tok(lex.next_token(), t(closebrace(), 38).with_coord(4, 0))
    stop(lex)

    lex = Lexer.new("{\n   z::\n       here's some\n     text\n}\n")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("z"), 5).with_coord(1, 3))
    lex = tok(lex.next_token(), t(dcolon(), 6, 8).with_coord(1, 4))
    lex = tok(
        lex.next_multistring(3),
        t(multistring("\n       here's some\n     text\n"), 8, 38).with_coord(1, 6),
    )
    lex = tok(lex.next_token(), t(closebrace(), 38).with_coord(4, 0))
    stop(lex)

    lex = Lexer.new("{\n    a:: x\n    b: y,\n}\n")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("a"), 6).with_coord(1, 4))
    lex = tok(lex.next_token(), t(dcolon(), 7, 9).with_coord(1, 5))
    lex = tok(lex.next_multistring(4), t(multistring(" x\n"), 9, 12).with_coord(1, 7))
    lex = tok(lex.next_key(), t(name("b"), 16).with_coord(2, 4))
    lex = tok(lex.next_token(), t(colon(), 17).with_coord(2, 5))
    lex = tok(lex.next_token(), t(name("y"), 19).with_coord(2, 7))
    lex = tok(lex.next_token(), t(comma(), 20).with_coord(2, 8))
    lex = tok(lex.next_token(), t(closebrace(), 22).with_coord(3, 0))
    stop(lex)

    lex = Lexer.new("{...y, x: 1}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(ellipsis(), 1, 4))
    lex = tok(lex.next_token(), t(name("y"), 4))
    lex = tok(lex.next_token(), t(comma(), 5))
    lex = tok(lex.next_key(), t(name("x"), 7))
    lex = tok(lex.next_token(), t(colon(), 8))
    lex = tok(lex.next_token(), t(int_("1"), 10))
    lex = tok(lex.next_token(), t(closebrace(), 11))
    stop(lex)

    lex = Lexer.new("{for [x,y] in z: x: y}")
    lex = tok(lex.next_token(), t(openbrace(), 0))
    lex = tok(lex.next_key(), t(name("for"), 1, 4))
    lex = tok(lex.next_token(), t(openbracket(), 5))
    lex = tok(lex.next_token(), t(name("x"), 6))
    lex = tok(lex.next_token(), t(comma(), 7))
    lex = tok(lex.next_token(), t(name("y"), 8))
    lex = tok(lex.next_token(), t(closebracket(), 9))
    lex = tok(lex.next_token(), t(name("in"), 11, 13))
    lex = tok(lex.next_token(), t(name("z"), 14))
    lex = tok(lex.next_token(), t(colon(), 15))
    lex = tok(lex.next_key(), t(name("x"), 17))
    lex = tok(lex.next_token(), t(colon(), 18))
    lex = tok(lex.next_token(), t(name("y"), 20))
    lex = tok(lex.next_token(), t(closebrace(), 21))
    stop(lex)
