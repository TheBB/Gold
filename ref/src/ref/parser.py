from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Callable

from .ast import (
    AlignSpec,
    ArgElement,
    Binding,
    BinOpTransform,
    BranchExpr,
    CondLE,
    CondME,
    EagerOp,
    File,
    FormatSpec,
    FormatTypeSpec,
    FunCallTransform,
    FunctionExpr,
    GroupingSpec,
    IdentifierBinding,
    IdentifierExpr,
    ImportStatement,
    InterpolateStringElement,
    KeywordAE,
    LetExpr,
    ListBEBinding,
    ListBESlurp,
    ListBESlurpTo,
    ListBinding,
    ListBindingElement,
    ListElement,
    ListExpr,
    ListPatternBinding,
    LiteralExpr,
    LogicOp,
    LoopLE,
    LoopME,
    MapBEBinding,
    MapBESlurpTo,
    MapBinding,
    MapBindingElement,
    MapElement,
    MapExpr,
    MapPatternBinding,
    RawStringElement,
    SignSpec,
    SingletonAE,
    SingletonLE,
    SingletonME,
    SplatAE,
    SplatLE,
    SplatME,
    StringElement,
    StringExpr,
    TopLevel,
    TransformedExpr,
    UnOp,
    UnOpTransform,
)
from .lexer import Lexer, LexError, Token, TokenType
from .span import Span, Tagged, tag

KEYWORDS: frozenset[str] = frozenset(
    [
        "for",
        "when",
        "if",
        "then",
        "else",
        "let",
        "in",
        "has",
        "true",
        "false",
        "null",
        "and",
        "or",
        "not",
        "as",
        "import",
        "fn",
    ]
)

# ── Public output types ───────────────────────────────────────────────────────


@dataclass(frozen=True)
class ParseError:
    """A parse error: a message and the source span it refers to."""

    span: Span
    message: str

    def __str__(self) -> str:
        s = self.span
        return f"{self.message} at {s.line + 1}:{s.column + 1}"


@dataclass(frozen=True)
class ParseResult:
    """
    Result of parsing a Gold source file.

    ``tree`` is non-None whenever any expression could be recovered.  It may
    contain ``LiteralExpr(None)`` sentinels at positions where sub-expressions
    were missing, so it is always structurally complete.

    ``errors`` is non-empty on invalid or incomplete input.  An LSP consumer
    should always render ``tree`` and surface ``errors`` as diagnostics.
    """

    tree: File | None
    errors: list[ParseError]

    @property
    def ok(self) -> bool:
        return not self.errors


# ── Helpers ───────────────────────────────────────────────────────────────────


def _multiline(s: str) -> str:
    """Strip common leading indentation from a raw multiline-string token."""
    lines = s.splitlines()
    if not lines:
        return ""
    first = lines[0].lstrip()
    rest = [ln for ln in lines[1:] if ln.strip()]
    indent = min((len(ln) - len(ln.lstrip()) for ln in rest), default=0)
    result = first
    for ln in rest:
        if result:
            result += "\n"
        result += ln[indent:]
    return result


# ── Parser ────────────────────────────────────────────────────────────────────


class Parser:
    """
    Recursive-descent parser for the Gold language.

    Designed for LSP use: always produces a (possibly partial) AST and
    accumulates errors rather than aborting on the first problem.

    Convention:
    - ``_try_*`` methods return ``T | None`` and never advance the lexer on
      failure.  They never add errors.
    - ``_parse_*`` / ``_require_*`` methods always return ``T``.  They add an
      error and return a sentinel value when a required piece is missing.
    - The lexer is only advanced on confirmed token consumption.
    """

    def __init__(self, source: str) -> None:
        self._lexer: Lexer = Lexer.new(source)
        self._errors: list[ParseError] = []

    # ── Error helpers ──────────────────────────────────────────────────────────

    def _error(self, span: Span, message: str) -> None:
        self._errors.append(ParseError(span=span, message=message))

    def _here(self) -> Span:
        return self._lexer.position.with_length(0)

    def _sentinel(self) -> Tagged[LiteralExpr]:
        """A null-literal sentinel used where a required expression is absent."""
        return tag(LiteralExpr(None), self._here())

    def _dummy_binding(self) -> Tagged[IdentifierBinding]:
        sp = self._here()
        return tag(IdentifierBinding(tag("_", sp)), sp)

    # ── Token helpers ──────────────────────────────────────────────────────────

    def _try_tok(self, kind: TokenType, mode: str = "default") -> Tagged[Token] | None:
        """
        Try to consume a token of ``kind`` in the given lexer mode.
        Returns the tagged token on success (advancing the lexer); None otherwise.
        """
        try:
            match mode:
                case "default":
                    lexer, tok = self._lexer.next_token()
                case "key":
                    lexer, tok = self._lexer.next_key()
                case "string":
                    lexer, tok = self._lexer.next_string()
                case "fmtspec":
                    lexer, tok = self._lexer.next_fmtspec()
                case _:
                    raise ValueError(f"unknown lex mode: {mode!r}")
            if tok.contents.kind == kind:
                self._lexer = lexer
                return tok
            return None
        except LexError:
            return None

    def _expect_tok(self, kind: TokenType, mode: str = "default") -> Tagged[Token]:
        """Consume a required token; record error and return dummy if missing."""
        tok = self._try_tok(kind, mode)
        if tok is not None:
            return tok
        sp = self._here()
        self._error(sp, f"expected {kind}")
        return tag(Token(kind, ""), sp)

    def _try_keyword(self, kw: str) -> Tagged[str] | None:
        try:
            lexer, tok = self._lexer.next_token()
            if tok.contents.kind == TokenType.Name and tok.contents.text == kw:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except LexError:
            return None

    def _try_map_keyword(self, kw: str) -> Tagged[str] | None:
        try:
            lexer, tok = self._lexer.next_key()
            if tok.contents.kind == TokenType.Name and tok.contents.text == kw:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except LexError:
            return None

    def _expect_keyword(self, kw: str) -> Tagged[str]:
        tok = self._try_keyword(kw)
        if tok is not None:
            return tok
        sp = self._here()
        self._error(sp, f"expected '{kw}'")
        return tag(kw, sp)

    def _try_identifier(self) -> Tagged[str] | None:
        """A Name token that is not a reserved keyword."""
        try:
            lexer, tok = self._lexer.next_token()
            if tok.contents.kind == TokenType.Name and tok.contents.text not in KEYWORDS:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except LexError:
            return None

    def _try_map_identifier(self) -> Tagged[str] | None:
        """Any Name token in map-key context (no keyword restriction)."""
        try:
            lexer, tok = self._lexer.next_key()
            if tok.contents.kind == TokenType.Name:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except LexError:
            return None

    # ── fmtspec helpers ────────────────────────────────────────────────────────

    def _fmtspec_try_char(self) -> str | None:
        try:
            lexer, tok = self._lexer.next_fmtspec()
            if tok.contents.kind == TokenType.Char:
                self._lexer = lexer
                return tok.contents.text
            return None
        except LexError:
            return None

    def _fmtspec_try_number(self) -> int | None:
        try:
            lexer, tok = self._lexer.next_fmtspec()
            if tok.contents.kind == TokenType.Integer:
                self._lexer = lexer
                return int(tok.contents.text)
            return None
        except LexError:
            return None

    # ── Format specifier ──────────────────────────────────────────────────────

    _ALIGN_CHARS = {
        "<": AlignSpec.Left,
        ">": AlignSpec.Right,
        "^": AlignSpec.Center,
        "=": AlignSpec.AfterSign,
    }
    _FMT_TYPE_CHARS = {
        "s": FormatTypeSpec.String,
        "b": FormatTypeSpec.Binary,
        "c": FormatTypeSpec.Character,
        "d": FormatTypeSpec.Decimal,
        "o": FormatTypeSpec.Octal,
        "x": FormatTypeSpec.HexLower,
        "X": FormatTypeSpec.HexUpper,
        "e": FormatTypeSpec.SciLower,
        "E": FormatTypeSpec.SciUpper,
        "f": FormatTypeSpec.Fixed,
        "g": FormatTypeSpec.General,
        "%": FormatTypeSpec.Percentage,
    }

    def _parse_format_spec(self) -> FormatSpec:
        """Parse a format-spec token stream (used after ':' in string interpolation)."""
        # fill + align: try (any-char, align-char) first, then just (align-char)
        saved0 = self._lexer
        fill_char: str | None = None
        align: AlignSpec | None = None
        c1 = self._fmtspec_try_char()
        if c1 is not None:
            c2 = self._fmtspec_try_char()
            if c2 is not None and c2 in self._ALIGN_CHARS:
                fill_char, align = c1, self._ALIGN_CHARS[c2]
            else:
                # c1 might itself be an alignment character
                self._lexer = saved0
                c = self._fmtspec_try_char()
                if c is not None and c in self._ALIGN_CHARS:
                    align = self._ALIGN_CHARS[c]
                else:
                    self._lexer = saved0  # nothing matched

        # sign: + - <space>
        saved = self._lexer
        c = self._fmtspec_try_char()
        sign: SignSpec | None = {"+": SignSpec.Plus, "-": SignSpec.Minus, " ": SignSpec.Space}.get(c or "")
        if sign is None:
            self._lexer = saved

        # alternate: #
        saved = self._lexer
        alternate = self._fmtspec_try_char() == "#"
        if not alternate:
            self._lexer = saved

        # zero-fill shorthand: 0 (sets fill='0', align=AfterSign when no explicit fill/align)
        saved = self._lexer
        zero = self._fmtspec_try_char() == "0"
        if not zero:
            self._lexer = saved

        width = self._fmtspec_try_number()

        # grouping: ,  _
        saved = self._lexer
        c = self._fmtspec_try_char()
        grouping: GroupingSpec | None = {",": GroupingSpec.Comma, "_": GroupingSpec.Underscore}.get(c or "")
        if grouping is None:
            self._lexer = saved

        # precision: . <int>
        precision: int | None = None
        saved = self._lexer
        if self._fmtspec_try_char() == ".":
            precision = self._fmtspec_try_number() or 0
        else:
            self._lexer = saved

        # type character
        saved = self._lexer
        c = self._fmtspec_try_char()
        fmt_type = self._FMT_TYPE_CHARS.get(c or "") if c else None
        if fmt_type is None:
            self._lexer = saved

        # Resolve fill and align, accounting for the zero shorthand
        has_explicit = fill_char is not None or align is not None
        fill = fill_char if fill_char is not None else ("0" if zero and not has_explicit else " ")
        final_align = align if has_explicit else (AlignSpec.AfterSign if zero else None)

        return FormatSpec(
            fill=fill,
            align=final_align,
            sign=sign,
            alternate=alternate,
            width=width,
            grouping=grouping,
            precision=precision,
            fmt_type=fmt_type,
        )

    # ── Strings ───────────────────────────────────────────────────────────────

    def _parse_raw_string_content(self) -> str:
        """Consume a StringLit token and decode its escape sequences."""
        tok = self._try_tok(TokenType.StringLit, mode="string")
        if tok is None:
            return ""
        out: list[str] = []
        i = 0
        text = tok.contents.text
        while i < len(text):
            if text[i] == "\\" and i + 1 < len(text):
                nc = text[i + 1]
                if nc in ('"', "\\", "$"):
                    out.append(nc)
                    i += 2
                    continue
            out.append(text[i])
            i += 1
        return "".join(out)

    def _parse_string_interp(self) -> StringElement | None:
        """Parse ``${ expr }`` or ``${ expr : fmtspec }``."""
        dollar = self._try_tok(TokenType.Dollar, mode="string")
        if dollar is None:
            return None
        self._expect_tok(TokenType.OpenBrace)
        expr = self._require_expr()
        fmt: FormatSpec | None = None
        if self._try_tok(TokenType.Colon) is not None:
            fmt = self._parse_format_spec()
            self._expect_tok(TokenType.CloseBrace, mode="fmtspec")
        else:
            self._expect_tok(TokenType.CloseBrace)
        return InterpolateStringElement(expr=expr, fmt=fmt)

    def _parse_string_part(self) -> Tagged[list[StringElement]] | None:
        """Parse one ``"..."`` string part; returns elements tagged with outer span."""
        open_q = self._try_tok(TokenType.DoubleQuote)
        if open_q is None:
            return None
        elements: list[StringElement] = []
        while True:
            interp = self._parse_string_interp()
            if interp is not None:
                elements.append(interp)
                continue
            raw = self._parse_raw_string_content()
            if raw:
                elements.append(RawStringElement(raw))
                continue
            break
        close_q = self._expect_tok(TokenType.DoubleQuote, mode="string")
        span = Span.covering(open_q.span, close_q.span)
        return tag(elements, span)

    def _try_string(self) -> Tagged[LiteralExpr | StringExpr] | None:
        """Parse one or more adjacent string parts (adjacent strings are concatenated)."""
        first = self._parse_string_part()
        if first is None:
            return None
        all_elements: list[StringElement] = list(first.contents)
        last_span = first.span
        while True:
            more = self._parse_string_part()
            if more is None:
                break
            all_elements.extend(more.contents)
            last_span = more.span
        span = Span.covering(first.span, last_span)
        return self._make_string_expr(all_elements, span)

    @staticmethod
    def _make_string_expr(elements: list[StringElement], span: Span) -> Tagged[LiteralExpr | StringExpr]:
        if not elements:
            return tag(LiteralExpr(""), span)
        if len(elements) == 1 and isinstance(elements[0], RawStringElement):
            return tag(LiteralExpr(elements[0].value), span)
        return tag(StringExpr(elements), span)

    # ── Numbers / atomics ─────────────────────────────────────────────────────

    def _try_number(self) -> Tagged[LiteralExpr] | None:
        tok = self._try_tok(TokenType.Float)
        if tok is not None:
            try:
                return tok.map(lambda t: LiteralExpr(float(t.text.replace("_", ""))))
            except ValueError:
                pass
        tok = self._try_tok(TokenType.Integer)
        if tok is not None:
            try:
                return tok.map(lambda t: LiteralExpr(int(t.text.replace("_", ""))))
            except ValueError:
                pass
        return None

    def _try_atomic(self) -> Tagged[LiteralExpr] | None:
        """null | true | false | number | string."""
        for kw, val in (("null", None), ("true", True), ("false", False)):
            tok = self._try_keyword(kw)
            if tok is not None:
                return tok.map(lambda _: LiteralExpr(val))
        n = self._try_number()
        if n is not None:
            return n
        s = self._try_string()
        if s is not None:
            return s  # type: ignore[return-value]
        return None

    # ── List ──────────────────────────────────────────────────────────────────

    def _parse_list_element(self) -> Tagged[ListElement] | None:
        # Splat
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            expr = self._require_expr()
            return tag(SplatLE(expr=expr), Span.covering(ellipsis.span, expr.span))

        # For-loop: for binding in iterable : element
        if (kw := self._try_keyword("for")) is not None:
            binding = self._require_binding()
            self._expect_keyword("in")
            iterable = self._require_expr()
            self._expect_tok(TokenType.Colon)
            element = self._require_list_element()
            return tag(
                LoopLE(binding=binding, iterable=iterable, element=element),
                Span.covering(kw.span, element.span),
            )

        # When-guard: when expr : element
        if (kw := self._try_keyword("when")) is not None:
            condition = self._require_expr()
            self._expect_tok(TokenType.Colon)
            element = self._require_list_element()
            return tag(CondLE(condition=condition, element=element), Span.covering(kw.span, element.span))

        # Singleton
        expr = self._try_expr()
        if expr is None:
            return None
        return expr.wrap(SingletonLE)

    def _require_list_element(self) -> Tagged[ListElement]:
        el = self._parse_list_element()
        if el is not None:
            return el
        sp = self._here()
        self._error(sp, "expected list element")
        return tag(SingletonLE(self._sentinel()), sp)

    def _try_list(self) -> Tagged[ListExpr] | None:
        open_b = self._try_tok(TokenType.OpenBracket)
        if open_b is None:
            return None
        elements: list[Tagged[ListElement]] = []
        while True:
            # Peek for close (handles empty and trailing-comma cases)
            saved = self._lexer
            if self._try_tok(TokenType.CloseBracket) is not None:
                self._lexer = saved  # restore; let the explicit expect below consume it
                break
            el = self._parse_list_element()
            if el is None:
                break
            elements.append(el)
            if self._try_tok(TokenType.Comma) is None:
                break
        close_b = self._expect_tok(TokenType.CloseBracket)
        return tag(ListExpr(elements), Span.covering(open_b.span, close_b.span))

    # ── Map ───────────────────────────────────────────────────────────────────

    def _parse_map_key(self) -> Tagged | None:
        """Parse a literal map key: string | identifier (does NOT handle ``$`` prefix)."""
        s = self._try_string()
        if s is not None:
            return s
        name = self._try_map_identifier()
        if name is not None:
            return name.map(LiteralExpr)
        return None

    def _parse_map_element(self) -> tuple[Tagged[MapElement], bool] | None:
        """
        Parse one map element; returns ``(element, skip_separator)``.
        ``skip_separator`` is True for ``key :: multiline`` entries.
        """
        self._lexer = self._lexer.skip_whitespace()

        # Splat
        if (ellipsis := self._try_tok(TokenType.Ellipsis, mode="key")) is not None:
            expr = self._require_expr()
            return tag(SplatME(expr=expr), Span.covering(ellipsis.span, expr.span)), False

        # For-loop
        if (kw := self._try_map_keyword("for")) is not None:
            binding = self._require_binding()
            self._expect_keyword("in")
            iterable = self._require_expr()
            self._expect_tok(TokenType.Colon)
            inner, skip = self._require_map_element()
            return tag(
                LoopME(binding=binding, iterable=iterable, element=inner), Span.covering(kw.span, inner.span)
            ), skip

        # When-guard
        if (kw := self._try_map_keyword("when")) is not None:
            condition = self._require_expr()
            self._expect_tok(TokenType.Colon)
            inner, skip = self._require_map_element()
            return tag(CondME(condition=condition, element=inner), Span.covering(kw.span, inner.span)), skip

        # Dynamic key: $identifier or $(expr)
        if (dollar := self._try_tok(TokenType.Dollar, mode="key")) is not None:
            if self._try_tok(TokenType.OpenParen) is not None:
                inner_expr = self._require_expr()
                self._expect_tok(TokenType.CloseParen)
                key: Tagged = inner_expr
            else:
                ident_name = self._try_identifier()
                if ident_name is None:
                    self._error(self._here(), "expected expression")
                    return tag(SingletonME(key=self._sentinel(), value=self._sentinel()), dollar.span), False
                key = ident_name.wrap(IdentifierExpr)
            elem_start = dollar.span
            col = key.span.column
            self._expect_tok(TokenType.Colon, mode="key")
            value = self._require_expr()
            return tag(SingletonME(key=key, value=value), Span.covering(elem_start, value.span)), False

        # Literal key: string | identifier
        lit_key = self._parse_map_key()
        if lit_key is None:
            return None
        key = lit_key

        elem_start = key.span
        col = key.span.column

        # :: multiline (no separator needed after)
        if self._try_tok(TokenType.DoubleColon, mode="key") is not None:
            try:
                ms_lexer, ms_tok = self._lexer.next_multistring(col)
                self._lexer = ms_lexer
                val_str = _multiline(ms_tok.contents.text)
                value = tag(LiteralExpr(val_str), ms_tok.span)
            except LexError:
                value = self._sentinel()
                self._error(self._here(), "expected multiline string")
            return tag(SingletonME(key=key, value=value), Span.covering(elem_start, value.span)), True

        # : expr
        self._expect_tok(TokenType.Colon, mode="key")
        value = self._require_expr()
        return tag(SingletonME(key=key, value=value), Span.covering(elem_start, value.span)), False

    def _require_map_element(self) -> tuple[Tagged[MapElement], bool]:
        el = self._parse_map_element()
        if el is not None:
            return el
        sp = self._here()
        self._error(sp, "expected map element")
        dummy_key: Tagged[LiteralExpr] = tag(LiteralExpr(""), sp)
        return tag(SingletonME(key=dummy_key, value=self._sentinel()), sp), False

    def _try_map(self) -> Tagged[MapExpr] | None:
        open_b = self._try_tok(TokenType.OpenBrace)
        if open_b is None:
            return None
        elements: list[Tagged[MapElement]] = []
        while True:
            saved = self._lexer
            if self._try_tok(TokenType.CloseBrace) is not None:
                self._lexer = saved
                break
            result = self._parse_map_element()
            if result is None:
                break
            el, skip_sep = result
            elements.append(el)
            if skip_sep:
                continue
            if self._try_tok(TokenType.Comma) is None:
                break
        close_b = self._expect_tok(TokenType.CloseBrace)
        return tag(MapExpr(elements), Span.covering(open_b.span, close_b.span))

    # ── Postfix expressions ───────────────────────────────────────────────────

    def _try_postfixable(self) -> Tagged | None:
        """paren | atomic | identifier | list | map."""
        if (open_p := self._try_tok(TokenType.OpenParen)) is not None:
            expr = self._require_expr()
            close_p = self._expect_tok(TokenType.CloseParen)
            return tag(expr.contents, Span.covering(open_p.span, close_p.span))

        a = self._try_atomic()
        if a is not None:
            return a

        ident = self._try_identifier()
        if ident is not None:
            return ident.wrap(IdentifierExpr)

        lst = self._try_list()
        if lst is not None:
            return lst

        mp = self._try_map()
        if mp is not None:
            return mp

        return None

    def _try_postfixed(self) -> Tagged | None:
        """postfixable followed by zero or more postfix operators."""
        expr = self._try_postfixable()
        if expr is None:
            return None

        while True:
            # .name  →  index by string literal
            if (dot := self._try_tok(TokenType.Dot)) is not None:
                name = self._try_identifier()
                if name is None:
                    self._error(self._here(), "expected identifier after '.'")
                    break
                key_expr: Tagged[LiteralExpr] = name.map(LiteralExpr)
                span = Span.covering(expr.span, name.span)
                expr = tag(
                    TransformedExpr(
                        operand=expr,
                        transform=BinOpTransform(op=tag(EagerOp.Index, dot.span), operand=key_expr),
                    ),
                    span,
                )
                continue

            # [subscript]
            if (open_b := self._try_tok(TokenType.OpenBracket)) is not None:
                subscript = self._require_expr()
                close_b = self._expect_tok(TokenType.CloseBracket)
                op_span = Span.covering(open_b.span, close_b.span)
                expr = tag(
                    TransformedExpr(
                        operand=expr,
                        transform=BinOpTransform(op=tag(EagerOp.Index, op_span), operand=subscript),
                    ),
                    Span.covering(expr.span, close_b.span),
                )
                continue

            # (args...)
            if (open_p := self._try_tok(TokenType.OpenParen)) is not None:
                args = self._parse_arg_list()
                close_p = self._expect_tok(TokenType.CloseParen)
                call_span = Span.covering(open_p.span, close_p.span)
                expr = tag(
                    TransformedExpr(
                        operand=expr,
                        transform=FunCallTransform(args=tag(args, call_span)),
                    ),
                    Span.covering(expr.span, close_p.span),
                )
                continue

            break
        return expr

    def _parse_arg_list(self) -> list[Tagged[ArgElement]]:
        args: list[Tagged[ArgElement]] = []
        while True:
            saved = self._lexer
            if self._try_tok(TokenType.CloseParen) is not None:
                self._lexer = saved
                break
            arg = self._parse_function_arg()
            if arg is None:
                break
            args.append(arg)
            if self._try_tok(TokenType.Comma) is None:
                break
        return args

    def _parse_function_arg(self) -> Tagged[ArgElement] | None:
        # Splat
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            expr = self._require_expr()
            return tag(SplatAE(expr=expr), Span.covering(ellipsis.span, expr.span))

        # Keyword arg: name: expr — only when ':' immediately follows the name
        saved = self._lexer
        name = self._try_identifier()
        if name is not None:
            if self._try_tok(TokenType.Colon) is not None:
                expr = self._require_expr()
                return tag(KeywordAE(key=name, expr=expr), Span.covering(name.span, expr.span))
            self._lexer = saved  # not a keyword arg; restore and fall through

        expr = self._try_expr()
        if expr is None:
            return None
        return expr.wrap(SingletonAE)

    # ── Operator precedence ───────────────────────────────────────────────────

    def _try_power(self) -> Tagged | None:
        """postfixed (^ prefixed)* — right-associative."""
        base = self._try_postfixed()
        if base is None:
            return None
        if (caret := self._try_tok(TokenType.Caret)) is None:
            return base
        rhs = self._try_prefixed()
        if rhs is None:
            self._error(self._here(), "expected operand after '^'")
            rhs = self._sentinel()
        return tag(
            TransformedExpr(
                operand=base,
                transform=BinOpTransform(op=tag(EagerOp.Power, caret.span), operand=rhs),
            ),
            Span.covering(base.span, rhs.span),
        )

    def _try_prefixed(self) -> Tagged | None:
        """(unary-op)* power."""
        ops: list[Tagged[UnOp | None]] = []
        while True:
            if (tok := self._try_tok(TokenType.Plus)) is not None:
                ops.append(tag(None, tok.span))
            elif (tok := self._try_tok(TokenType.Minus)) is not None:
                ops.append(tag(UnOp.ArithmeticalNegate, tok.span))
            elif (tok := self._try_keyword("not")) is not None:
                ops.append(tag(UnOp.LogicalNegate, tok.span))
            else:
                break

        operand = self._try_power()
        if operand is None:
            if ops:
                self._error(self._here(), "expected operand")
                operand = self._sentinel()
            else:
                return None

        for op in reversed(ops):
            span = Span.covering(op.span, operand.span)
            operand = tag(TransformedExpr(operand=operand, transform=UnOpTransform(op=op)), span)
        return operand

    def _try_lbinop(
        self,
        sub: Callable[[], Tagged | None],
        ops: dict[TokenType | str, EagerOp | LogicOp],
    ) -> Tagged | None:
        """Generic left-associative binary operator level."""
        lhs = sub()
        if lhs is None:
            return None
        while True:
            matched_op: EagerOp | LogicOp | None = None
            op_tok: Tagged | None = None
            for key, op_val in ops.items():
                t = self._try_keyword(key) if isinstance(key, str) else self._try_tok(key)
                if t is not None:
                    matched_op, op_tok = op_val, t
                    break
            if op_tok is None:
                break
            rhs = sub()
            if rhs is None:
                self._error(self._here(), "expected operand")
                rhs = self._sentinel()
            assert matched_op is not None
            lhs = tag(
                TransformedExpr(
                    operand=lhs,
                    transform=BinOpTransform(op=tag(matched_op, op_tok.span), operand=rhs),
                ),
                Span.covering(lhs.span, rhs.span),
            )
        return lhs

    def _try_product(self) -> Tagged | None:
        return self._try_lbinop(
            self._try_prefixed,
            {
                TokenType.Asterisk: EagerOp.Multiply,
                TokenType.DoubleSlash: EagerOp.IntegerDivide,
                TokenType.Slash: EagerOp.Divide,
            },
        )

    def _try_sum(self) -> Tagged | None:
        return self._try_lbinop(
            self._try_product,
            {
                TokenType.Plus: EagerOp.Add,
                TokenType.Minus: EagerOp.Subtract,
            },
        )

    def _try_inequality(self) -> Tagged | None:
        return self._try_lbinop(
            self._try_sum,
            {
                TokenType.LessEq: EagerOp.LessEqual,
                TokenType.Less: EagerOp.Less,
                TokenType.GreaterEq: EagerOp.GreaterEqual,
                TokenType.Greater: EagerOp.Greater,
            },
        )

    def _try_equality(self) -> Tagged | None:
        return self._try_lbinop(
            self._try_inequality,
            {
                TokenType.DoubleEq: EagerOp.Equal,
                TokenType.ExclamEq: EagerOp.NotEqual,
            },
        )

    def _try_contains(self) -> Tagged | None:
        return self._try_lbinop(self._try_equality, {"has": EagerOp.Contains})

    def _try_conjunction(self) -> Tagged | None:
        return self._try_lbinop(self._try_contains, {"and": LogicOp.And})

    def _try_disjunction(self) -> Tagged | None:
        return self._try_lbinop(self._try_conjunction, {"or": LogicOp.Or})

    # ── Composite expressions ─────────────────────────────────────────────────

    def _try_let(self) -> Tagged[LetExpr] | None:
        """let binding = expr … in expr"""
        first_kw = self._try_keyword("let")
        if first_kw is None:
            return None
        bindings: list[tuple[Tagged[Binding], Tagged]] = []
        kw: Tagged[str] | None = first_kw
        while kw is not None:
            b = self._require_binding()
            self._expect_tok(TokenType.Eq)
            val = self._require_expr()
            bindings.append((b, val))
            kw = self._try_keyword("let")
        self._expect_keyword("in")
        body = self._require_expr()
        return tag(LetExpr(bindings=bindings, expression=body), Span.covering(first_kw.span, body.span))

    def _try_branch(self) -> Tagged[BranchExpr] | None:
        """if cond then expr else expr"""
        kw = self._try_keyword("if")
        if kw is None:
            return None
        cond = self._require_expr()
        self._expect_keyword("then")
        true_br = self._require_expr()
        self._expect_keyword("else")
        false_br = self._require_expr()
        return tag(
            BranchExpr(condition=cond, true_branch=true_br, false_branch=false_br),
            Span.covering(kw.span, false_br.span),
        )

    def _try_function(self) -> Tagged[FunctionExpr] | None:
        return self._try_fn_new_style() or self._try_fn_old_kw_style() or self._try_fn_old_pos_style()

    # ── Binding helpers used by function parsers ───────────────────────────────

    def _parse_list_binding_terminated(
        self,
        try_close: Callable[[], Tagged | None],
        start_span: Span | None = None,
    ) -> tuple[Tagged[ListBinding], Tagged | None]:
        """
        Parse list-binding elements until ``try_close()`` succeeds or no more
        elements can be parsed.

        ``start_span`` should be the span of the opening delimiter so that the
        returned binding's span covers delimiters on both sides.

        Returns ``(list_binding, close_token_or_None)``.  When ``close_token``
        is not None the terminator has already been consumed.
        """
        elements: list[Tagged[ListBindingElement]] = []
        inner_start = self._here()
        close: Tagged | None = None

        while True:
            # Try close first (empty list / trailing comma)
            close = try_close()
            if close is not None:
                break  # terminator consumed; stop

            el = self._try_list_binding_element()
            if el is None:
                self._error(self._here(), "expected parameter or closing delimiter")
                close = try_close()
                break
            elements.append(el)

            if self._try_tok(TokenType.Comma) is None:
                close = try_close()
                if close is None:
                    self._error(self._here(), "expected ',' or closing delimiter")
                break

        end_sp = close.span if close is not None else self._here()
        actual_start = start_span if start_span is not None else inner_start
        span = Span.covering(actual_start, end_sp)
        return tag(ListBinding(elements), span), close

    def _parse_map_binding_terminated(
        self,
        try_close: Callable[[], Tagged | None],
        start_span: Span | None = None,
    ) -> tuple[Tagged[MapBinding], Tagged | None]:
        """Same pattern for map bindings."""
        elements: list[Tagged[MapBindingElement]] = []
        inner_start = self._here()
        close: Tagged | None = None

        while True:
            close = try_close()
            if close is not None:
                break

            el = self._try_map_binding_element()
            if el is None:
                self._error(self._here(), "expected parameter or closing delimiter")
                close = try_close()
                break
            elements.append(el)

            if self._try_tok(TokenType.Comma) is None:
                close = try_close()
                if close is None:
                    self._error(self._here(), "expected ',' or closing delimiter")
                break

        end_sp = close.span if close is not None else self._here()
        actual_start = start_span if start_span is not None else inner_start
        span = Span.covering(actual_start, end_sp)
        return tag(MapBinding(elements), span), close

    # ── Function syntax variants ───────────────────────────────────────────────

    def _try_fn_new_style(self) -> Tagged[FunctionExpr] | None:
        """fn ( pos ; kw ) body  |  fn { kw } body"""
        fn_kw = self._try_keyword("fn")
        if fn_kw is None:
            return None

        if (open_p := self._try_tok(TokenType.OpenParen)) is not None:
            # Positional params, terminated by ) or ;
            pos, term = self._parse_list_binding_terminated(
                lambda: self._try_tok(TokenType.CloseParen) or self._try_tok(TokenType.SemiColon),
                start_span=open_p.span,
            )
            kw: Tagged[MapBinding] | None = None
            if term is not None and term.contents.text == ";":
                kw, close_p = self._parse_map_binding_terminated(
                    lambda: self._try_tok(TokenType.CloseParen),
                    start_span=term.span,
                )
                if close_p is None:
                    self._expect_tok(TokenType.CloseParen)
            elif term is None:
                self._expect_tok(TokenType.CloseParen)
            body = self._require_expr()
            return tag(
                FunctionExpr(positional=pos, keywords=kw, expression=body),
                Span.covering(fn_kw.span, body.span),
            )

        if (open_b := self._try_tok(TokenType.OpenBrace)) is not None:
            # Keyword-only function
            kw, close_b = self._parse_map_binding_terminated(
                lambda: self._try_tok(TokenType.CloseBrace),
                start_span=open_b.span,
            )
            if close_b is None:
                self._expect_tok(TokenType.CloseBrace)
            body = self._require_expr()
            empty_pos = tag(ListBinding([]), open_b.span)
            return tag(
                FunctionExpr(positional=empty_pos, keywords=kw, expression=body),
                Span.covering(fn_kw.span, body.span),
            )

        self._error(self._here(), "expected '(' or '{' after 'fn'")
        return tag(
            FunctionExpr(
                positional=tag(ListBinding([]), fn_kw.span),
                keywords=None,
                expression=self._sentinel(),
            ),
            fn_kw.span,
        )

    def _try_fn_old_kw_style(self) -> Tagged[FunctionExpr] | None:
        """{| kw_params |} body  (deprecated syntax)"""
        open_bp = self._try_tok(TokenType.OpenBracePipe)
        if open_bp is None:
            return None
        kw, close_bp = self._parse_map_binding_terminated(
            lambda: self._try_tok(TokenType.CloseBracePipe),
            start_span=open_bp.span,
        )
        if close_bp is None:
            self._expect_tok(TokenType.CloseBracePipe)
        body = self._require_expr()
        empty_pos = tag(ListBinding([]), open_bp.span.with_length(1))
        return tag(
            FunctionExpr(positional=empty_pos, keywords=kw, expression=body),
            Span.covering(open_bp.span, body.span),
        )

    def _try_fn_old_pos_style(self) -> Tagged[FunctionExpr] | None:
        """| pos ; kw | body  (deprecated syntax)"""
        open_pipe = self._try_tok(TokenType.Pipe)
        if open_pipe is None:
            return None
        pos, term = self._parse_list_binding_terminated(
            lambda: self._try_tok(TokenType.Pipe) or self._try_tok(TokenType.SemiColon),
            start_span=open_pipe.span,
        )
        kw: Tagged[MapBinding] | None = None
        if term is not None and term.contents.text == ";":
            kw, close_pipe = self._parse_map_binding_terminated(
                lambda: self._try_tok(TokenType.Pipe),
                start_span=term.span,
            )
            if close_pipe is None:
                self._expect_tok(TokenType.Pipe)
        elif term is None:
            self._expect_tok(TokenType.Pipe)
        body = self._require_expr()
        return tag(
            FunctionExpr(positional=pos, keywords=kw, expression=body),
            Span.covering(open_pipe.span, body.span),
        )

    # ── Top-level expression ───────────────────────────────────────────────────

    def _try_expr(self) -> Tagged | None:
        return self._try_let() or self._try_branch() or self._try_function() or self._try_disjunction()

    def _require_expr(self) -> Tagged:
        expr = self._try_expr()
        if expr is not None:
            return expr
        sp = self._here()
        self._error(sp, "expected expression")
        return self._sentinel()

    # ── Bindings ──────────────────────────────────────────────────────────────

    def _try_list_binding_element(self) -> Tagged[ListBindingElement] | None:
        # Slurp: ...name  or  ...
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            name = self._try_identifier()
            if name is not None:
                return tag(ListBESlurpTo(name=name.contents), Span.covering(ellipsis.span, name.span))
            return tag(ListBESlurp(), ellipsis.span)

        b = self._try_binding()
        if b is None:
            return None
        if self._try_tok(TokenType.Eq) is not None:
            default = self._require_expr()
            return tag(ListBEBinding(binding=b, default=default), Span.covering(b.span, default.span))
        return tag(ListBEBinding(binding=b, default=None), b.span)

    def _try_map_binding_element(self) -> Tagged[MapBindingElement] | None:
        # Named slurp: ...name
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            name = self._try_identifier()
            if name is None:
                self._error(self._here(), "expected identifier after '...'")
                return tag(MapBESlurpTo(name="_"), ellipsis.span)
            return tag(MapBESlurpTo(name=name.contents), Span.covering(ellipsis.span, name.span))

        # name (as binding)? (= default)?
        name = self._try_identifier()
        if name is None:
            return None

        sub_binding: Tagged[Binding] | None = None
        if self._try_keyword("as") is not None:
            sub_binding = self._require_binding()

        default: Tagged | None = None
        if self._try_tok(TokenType.Eq) is not None:
            default = self._require_expr()

        if sub_binding is None:
            sub_binding = tag(IdentifierBinding(name=name), name.span)

        end = (default or sub_binding).span
        return tag(
            MapBEBinding(key=name, binding=sub_binding, default=default), Span.covering(name.span, end)
        )

    def _try_binding(self) -> Tagged[Binding] | None:
        # Identifier
        name = self._try_identifier()
        if name is not None:
            return tag(IdentifierBinding(name=name), name.span)

        # List pattern: [ ... ]
        if (open_b := self._try_tok(TokenType.OpenBracket)) is not None:
            lb, close = self._parse_list_binding_terminated(
                lambda: self._try_tok(TokenType.CloseBracket),
                start_span=open_b.span,
            )
            if close is None:
                close = self._expect_tok(TokenType.CloseBracket)
            return tag(ListPatternBinding(binding=lb), Span.covering(open_b.span, close.span))

        # Map pattern: { ... }
        if (open_b := self._try_tok(TokenType.OpenBrace)) is not None:
            mb, close = self._parse_map_binding_terminated(
                lambda: self._try_tok(TokenType.CloseBrace),
                start_span=open_b.span,
            )
            if close is None:
                close = self._expect_tok(TokenType.CloseBrace)
            return tag(MapPatternBinding(binding=mb), Span.covering(open_b.span, close.span))

        return None

    def _require_binding(self) -> Tagged[Binding]:
        b = self._try_binding()
        if b is not None:
            return b
        sp = self._here()
        self._error(sp, "expected binding")
        return self._dummy_binding()

    # ── Top-level statements ───────────────────────────────────────────────────

    def _try_import(self) -> ImportStatement | None:
        """import "path" as binding"""
        if self._try_keyword("import") is None:
            return None
        open_q = self._expect_tok(TokenType.DoubleQuote)
        path_str = self._parse_raw_string_content()
        close_q = self._expect_tok(TokenType.DoubleQuote, mode="string")
        path: Tagged[str] = tag(path_str, Span.covering(open_q.span, close_q.span))
        self._expect_keyword("as")
        binding = self._require_binding()
        return ImportStatement(path=path, binding=binding)

    def parse_file(self) -> File | None:
        """Parse a complete Gold file: imports* expression."""
        statements: list[TopLevel] = []
        while True:
            stmt = self._try_import()
            if stmt is None:
                break
            statements.append(stmt)

        expr = self._try_expr()
        if expr is None:
            if not statements:
                return None
            self._error(self._here(), "expected expression")
            expr = self._sentinel()

        return File(statements=statements, expression=expr)


# ── Public API ────────────────────────────────────────────────────────────────


def parse(source: str) -> ParseResult:
    """
    Parse a Gold source string and return a ``ParseResult``.

    The result always contains a structurally complete AST (``tree``), except
    when the input is entirely empty or unrecognisable.  Missing sub-expressions
    are replaced by ``LiteralExpr(None)`` sentinels.  All diagnostics are
    collected in ``result.errors`` with accurate source spans, making this
    suitable for powering LSP hover, diagnostics, and completion features.
    """
    parser = Parser(source)
    tree = parser.parse_file()
    return ParseResult(tree=tree, errors=parser._errors)
