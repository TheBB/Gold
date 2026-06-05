from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from functools import partial
from typing import TYPE_CHECKING, Unpack


if TYPE_CHECKING:
    from collections.abc import Callable, Iterator

from .ast import (
    AlignSpec,
    ArgElement,
    ArgKeyword,
    ArgSingleton,
    ArgSplat,
    Binding,
    BinOp,
    BinOpTransform,
    BranchExpr,
    EagerOp,
    Expr,
    File,
    FormatSpec,
    FormatTypeSpec,
    FunCallTransform,
    FunctionExpr,
    GroupingSpec,
    IdentifierBinding,
    IdentifierExpr,
    ImportStatement,
    LetExpr,
    ListBinding,
    ListBindingElement,
    ListBindingSingleton,
    ListBindingSlurp,
    ListBindingSlurpTo,
    ListCond,
    ListElement,
    ListExpr,
    ListLoop,
    ListPatternBinding,
    ListSingleton,
    ListSplat,
    LiteralExpr,
    LogicOp,
    MapBinding,
    MapBindingElement,
    MapBindingSingleton,
    MapBindingSlurpTo,
    MapCond,
    MapElement,
    MapExpr,
    MapLoop,
    MapPatternBinding,
    MapSingleton,
    MapSplat,
    MissingBinding,
    MissingExpr,
    SignSpec,
    StringElement,
    StringExpr,
    StringInterpolate,
    StringRaw,
    TopLevel,
    Transform,
    TransformedExpr,
    UnOp,
    UnOpTransform,
)
from .error import (
    Action,
    AnySyntaxElement,
    Error,
    Reason,
    SyntaxElement,
    SyntaxExpected,
)
from .lexer import Lexer, Token, TokenType
from .pprint import PrintOpts, pprint_parse_result
from .span import Paren, Span, Tagged, tag


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
class ParseResult:
    """
    Result of parsing a Gold source file.

    ``tree`` is non-None whenever any expression could be recovered.  It may
    contain ``MissingExpr`` and ``MissingBinding`` sentinels at positions where
    sub-expressions were absent, so it is always structurally complete.

    ``errors`` is non-empty on invalid or incomplete input.  An LSP consumer
    should always render ``tree`` and surface ``errors`` as diagnostics.
    """

    tree: File | None
    errors: list[Error]

    @property
    def ok(self) -> bool:
        return not self.errors

    def pprint(self, **kwargs: Unpack[PrintOpts]) -> str:
        return pprint_parse_result(self, **kwargs)

    def __str__(self) -> str:
        return self.pprint()


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


# ── Recovery ──────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class Recovery:
    parser: Parser
    lexer: Lexer

    def __call__(self) -> None:
        self.parser._lexer = self.lexer


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

    _lexer: Lexer
    _errors: list[Error]

    def __init__(self, source: str) -> None:
        self._lexer = Lexer.new(source)
        self._errors = []

    # ── Lexing context helper ──────────────────────────────────────────────────

    @contextmanager
    def _save(self) -> Iterator[Recovery]:
        recover = Recovery(self, self._lexer)
        try:
            yield recover
        except:
            recover()
            raise

    # ── Error helpers ──────────────────────────────────────────────────────────

    def error(self, span: Span, reason: Reason) -> None:
        self._errors.append(Error.new(reason).tag(span, Action.Parse))

    def loc(self) -> Span:
        return self._lexer.position.with_length(0)

    def missing_expr(self) -> Tagged[Expr]:
        """Sentinel for a required expression that could not be parsed."""
        return tag(MissingExpr(), self.loc())

    def missing_paren(self) -> Paren[Expr]:
        return Paren.naked(self.missing_expr())

    def missing_binding(self) -> Tagged[Binding]:
        return tag(MissingBinding(), self.loc())

    def at_eof(self) -> bool:
        """Return True if there is no more non-whitespace input."""
        return self._lexer.at_eof()

    def require[T](
        self,
        parser: Callable[[], T | None],
        fallback: Callable[[], T],
        reason: Callable[[], Reason],
    ) -> T:
        result = parser()
        if result is None:
            self.error(self.loc(), reason())
            return fallback()
        return result

    # ── Token helpers ──────────────────────────────────────────────────────────

    def try_token(self, kind: TokenType, mode: str = "default") -> Tagged[Token] | None:
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
        except Error:
            return None

    def require_token(self, kind: TokenType, mode: str = "default") -> Tagged[Token | None]:
        """Consume a required token; record error and return dummy if missing."""
        return self.require(
            partial(self.try_token, kind, mode),
            lambda: tag(None, self.loc()),
            lambda: SyntaxExpected(kind).reason(),
        )

    def try_keyword(self, kw: str) -> Tagged[str] | None:
        try:
            lexer, tok = self._lexer.next_token()
            if tok.contents.kind == TokenType.Name and tok.contents.text == kw:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except Error:
            return None

    def try_map_keyword(self, kw: str) -> Tagged[str] | None:
        try:
            lexer, tok = self._lexer.next_key()
            if tok.contents.kind == TokenType.Name and tok.contents.text == kw:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except Error:
            return None

    _KW_ELEMENTS: dict[str, AnySyntaxElement] = {
        "then": SyntaxElement.Then,
        "else": SyntaxElement.Else,
        "in": SyntaxElement.In,
        "as": SyntaxElement.As,
    }

    def require_keyword(self, kw: str) -> Tagged[str]:
        return self.require(
            partial(self.try_keyword, kw),
            lambda: tag(kw, self.loc()),
            lambda: SyntaxExpected(self._KW_ELEMENTS.get(kw, SyntaxElement.Expression)).reason(),
        )

    def try_identifier(self) -> Tagged[str] | None:
        """A Name token that is not a reserved keyword."""
        try:
            lexer, tok = self._lexer.next_token()
            if tok.contents.kind == TokenType.Name and tok.contents.text not in KEYWORDS:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except Error:
            return None

    def try_map_identifier(self) -> Tagged[str] | None:
        """Any Name token in map-key context (no keyword restriction)."""
        try:
            lexer, tok = self._lexer.next_key()
            if tok.contents.kind == TokenType.Name:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except Error:
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

    def try_fmtspec_char(self) -> str | None:
        try:
            lexer, tok = self._lexer.next_fmtspec()
            if tok.contents.kind == TokenType.Char:
                self._lexer = lexer
                return tok.contents.text
            return None
        except Error:
            return None

    def try_fmtspec_number(self) -> int | None:
        try:
            lexer, tok = self._lexer.next_fmtspec()
            if tok.contents.kind == TokenType.Integer:
                self._lexer = lexer
                return int(tok.contents.text)
            return None
        except Error:
            return None

    def try_fmtspec_fill_and_align(self) -> tuple[str, AlignSpec] | None:
        with self._save() as recover:
            c1 = self.try_fmtspec_char()
            c2 = self.try_fmtspec_char()
            if c1 is not None and c2 in self._ALIGN_CHARS:
                return c1, self._ALIGN_CHARS[c2]
            recover()
        return None

    def try_fmtspec_only_align(self) -> AlignSpec | None:
        with self._save() as recover:
            if (c := self.try_fmtspec_char()) in self._ALIGN_CHARS:
                return self._ALIGN_CHARS[c]
            recover()
        return None

    def try_fmtspec_fill_align(self) -> tuple[str | None, AlignSpec | None]:
        if (fa := self.try_fmtspec_fill_and_align()) is not None:
            return fa
        if (a := self.try_fmtspec_only_align()) is not None:
            return None, a
        return None, None

    def try_fmtspec_sign(self) -> SignSpec | None:
        with self._save() as recover:
            c = self.try_fmtspec_char()
            sign = {
                "+": SignSpec.Plus,
                "-": SignSpec.Minus,
                " ": SignSpec.Space,
            }.get(c or "")
            if sign is None:
                recover()
        return sign

    def try_fmtspec_alternate(self) -> bool:
        with self._save() as recover:
            if not (alternate := self.try_fmtspec_char() == "#"):
                recover()
        return alternate

    def try_fmtspec_zero(self) -> bool:
        with self._save() as recover:
            if not (zero := self.try_fmtspec_char() == "0"):
                recover()
        return zero

    def try_fmtspec_grouping(self) -> GroupingSpec | None:
        with self._save() as recover:
            c = self.try_fmtspec_char()
            grouping = {
                ",": GroupingSpec.Comma,
                "_": GroupingSpec.Underscore,
            }.get(c or "")
            if grouping is None:
                recover()
        return grouping

    def try_fmtspec_precision(self) -> int | None:
        with self._save() as recover:
            c = self.try_fmtspec_char()
            if c != ".":
                recover()
                return None
            n = self.try_fmtspec_number()
        return n or 0

    def try_fmtspec_type(self) -> FormatTypeSpec | None:
        with self._save() as recover:
            if (c := self.try_fmtspec_char()) in self._FMT_TYPE_CHARS:
                return self._FMT_TYPE_CHARS[c]
            recover()
        return None

    def require_fmtspec(self) -> FormatSpec:
        """Parse a format-spec token stream (used after ':' in string interpolation)."""
        # fill + align: try (any-char, align-char) first, then just (align-char)
        fill_char, align = self.try_fmtspec_fill_align()
        sign = self.try_fmtspec_sign()
        alternate = self.try_fmtspec_alternate()
        zero = self.try_fmtspec_zero()
        width = self.try_fmtspec_number()
        grouping = self.try_fmtspec_grouping()
        precision = self.try_fmtspec_precision()
        fmt_type = self.try_fmtspec_type()

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

    def try_raw_string_content(self) -> str | None:
        """Consume a StringLit token and decode its escape sequences."""
        if (tok := self.try_token(TokenType.StringLit, mode="string")) is None:
            return None
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

    def try_string_interp(self) -> StringElement | None:
        """Parse ``${ expr }`` or ``${ expr : fmtspec }``."""
        if self.try_token(TokenType.Dollar, mode="string") is None:
            return None
        self.require_token(TokenType.OpenBrace)
        expr = self.require_expr()
        fmt: FormatSpec | None = None
        if self.try_token(TokenType.Colon) is not None:
            fmt = self.require_fmtspec()
            self.require_token(TokenType.CloseBrace, mode="fmtspec")
        else:
            self.require_token(TokenType.CloseBrace)
        return StringInterpolate(expr=expr.inner(), fmt=fmt)

    def try_string_part(self) -> Tagged[list[StringElement]] | None:
        """Parse one ``"..."`` string part; returns elements tagged with outer span."""
        open_q = self.try_token(TokenType.DoubleQuote)
        if open_q is None:
            return None
        elements: list[StringElement] = []
        while True:
            if (interp := self.try_string_interp()) is not None:
                elements.append(interp)
                continue
            if (raw := self.try_raw_string_content()) is not None:
                elements.append(StringRaw(raw))
                continue
            break
        close_q = self.require_token(TokenType.DoubleQuote, mode="string")
        span = Span.covering(open_q.span, close_q.span)
        return tag(elements, span)

    def try_string(self) -> Tagged[Expr] | None:
        """Parse one or more adjacent string parts (adjacent strings are concatenated)."""
        first = self.try_string_part()
        if first is None:
            return None
        all_elements: list[StringElement] = list(first.contents)
        last_span = first.span
        while True:
            if (more := self.try_string_part()) is None:
                break
            all_elements.extend(more.contents)
            last_span = more.span
        span = Span.covering(first.span, last_span)
        return self.make_string_expr(all_elements, span)

    @staticmethod
    def make_string_expr(elements: list[StringElement], span: Span) -> Tagged[Expr]:
        if not elements:
            return tag(LiteralExpr(""), span)
        if len(elements) == 1 and isinstance(elements[0], StringRaw):
            return tag(LiteralExpr(elements[0].value), span)
        return tag(StringExpr(elements), span)

    # ── Numbers / atomics ─────────────────────────────────────────────────────

    def try_number(self) -> Tagged[Expr] | None:
        if (tok := self.try_token(TokenType.Float)) is not None:
            try:
                return tok.map(lambda t: LiteralExpr(float(t.text.replace("_", ""))))
            except ValueError:
                pass
        if (tok := self.try_token(TokenType.Integer)) is not None:
            try:
                return tok.map(lambda t: LiteralExpr(int(t.text.replace("_", ""))))
            except ValueError:
                pass
        return None

    def try_atomic(self) -> Tagged[Expr] | None:
        """null | true | false | number | string."""
        for kw, val in (("null", None), ("true", True), ("false", False)):
            if (tok := self.try_keyword(kw)) is not None:
                return tok.map(lambda _: LiteralExpr(val))
        if (n := self.try_number()) is not None:
            return n
        if (s := self.try_string()) is not None:
            return s
        return None

    # ── Separated-list kernel ─────────────────────────────────────────────────

    def seplist_inner[T](
        self,
        try_item: Callable[[], tuple[T, bool] | None],
        try_sep: Callable[[], Tagged[Token] | None],
        try_close: Callable[[], Tagged[Token] | None],
        err_missing_item: Reason,
        err_missing_sep: Reason,
        close_tok_type: TokenType,
    ) -> tuple[list[T], Tagged[Token | None]]:
        """
        Parse a comma-separated body without the opening delimiter.

        Always returns a close token — real on success, Tagged[None]
        (with error recorded) when the terminator is absent.

        try_item returns (item, skip_sep).  skip_sep=True skips the following
        separator check (used by map multiline entries).

        Recovery: if an item is followed by neither a separator nor the
        terminator but another item CAN be parsed, err_missing_sep is recorded
        and parsing continues.  If nothing follows, we break silently.
        """
        items: list[T] = []
        close: Tagged[Token] | None = None
        need_sep = False

        while True:
            if not need_sep:
                if (close := try_close()) is not None:
                    break
                if (result := try_item()) is None:
                    if err_missing_item is not None:
                        self.error(self.loc(), err_missing_item)
                        if (close := try_close()) is None:
                            close = tag(Token(close_tok_type, ""), self.loc())
                    else:
                        close = try_close()
                    break
                item, skip = result
                items.append(item)
                need_sep = not skip
            else:
                if try_sep() is not None:
                    need_sep = False
                    continue
                if (close := try_close()) is not None:
                    break
                # No sep and no close — peek for a following item.
                sep_pos = self.loc()
                saved = self._lexer
                if (result := try_item()) is None:
                    self._lexer = saved  # restore; break silently
                    break
                self.error(sep_pos, err_missing_sep)
                item, skip = result
                items.append(item)
                need_sep = not skip

        return items, close or self.require_token(close_tok_type)

    def try_seplist[T](
        self,
        try_open: Callable[[], Tagged | None],
        try_item: Callable[[], tuple[T, bool] | None],
        try_sep: Callable[[], Tagged[Token] | None],
        try_close: Callable[[], Tagged[Token] | None],
        err_missing_item: Reason,
        err_missing_sep: Reason,
        close_tok_type: TokenType,
    ) -> tuple[Tagged, list[T], Tagged[Token | None]] | None:
        """
        Parse a delimited, separated list.  Returns None when the opening
        delimiter is absent; otherwise (open, items, close).
        """
        open_tok = try_open()
        if open_tok is None:
            return None
        items, close_tok = self.seplist_inner(
            try_item,
            try_sep,
            try_close,
            err_missing_item,
            err_missing_sep,
            close_tok_type,
        )
        return open_tok, items, close_tok

    # ── List ──────────────────────────────────────────────────────────────────

    def try_list_element(self) -> Paren[ListElement] | None:
        # Splat
        if (ellipsis := self.try_token(TokenType.Ellipsis)) is not None:
            expr = self.require_expr()
            return Paren.naked(tag(ListSplat(expr=expr.inner()), Span.covering(ellipsis.span, expr.outer())))

        # For-loop: for binding in iterable : element
        if (kw := self.try_keyword("for")) is not None:
            binding = self.require_binding()
            self.require_keyword("in")
            iterable = self.require_expr()
            self.require_token(TokenType.Colon)
            element = self.require_list_element()
            return Paren.naked(
                tag(
                    ListLoop(binding=binding, iterable=iterable.inner(), element=element.inner()),
                    Span.covering(kw.span, element.outer()),
                )
            )

        # When-guard: when expr : element
        if (kw := self.try_keyword("when")) is not None:
            condition = self.require_expr()
            self.require_token(TokenType.Colon)
            element = self.require_list_element()
            return Paren.naked(
                tag(
                    ListCond(condition=condition.inner(), element=element.inner()),
                    Span.covering(kw.span, element.outer()),
                )
            )

        # Singleton
        expr = self.try_expr()
        if expr is None:
            return None
        return expr.map_wrap(ListSingleton)

    def require_list_element(self) -> Paren[ListElement]:
        return self.require(
            self.try_list_element,
            lambda: Paren.naked(tag(ListSingleton(self.missing_expr()), self.loc())),
            lambda: SyntaxExpected(SyntaxElement.ListElement).reason(),
        )

    def try_list(self) -> Tagged[Expr] | None:
        def try_item() -> tuple[Tagged[ListElement], bool] | None:
            el = self.try_list_element()
            return None if el is None else (el.inner(), False)

        result = self.try_seplist(
            partial(self.try_token, TokenType.OpenBracket),
            try_item,
            partial(self.try_token, TokenType.Comma),
            partial(self.try_token, TokenType.CloseBracket),
            SyntaxExpected(TokenType.CloseBracket, SyntaxElement.ListElement).reason(),
            SyntaxExpected(TokenType.Comma, TokenType.CloseBracket).reason(),
            close_tok_type=TokenType.CloseBracket,
        )
        if result is None:
            return None
        open_b, elements, close = result
        return tag(ListExpr(elements), Span.covering(open_b.span, close.span))

    # ── Map ───────────────────────────────────────────────────────────────────

    def try_map_key(self) -> Tagged[Expr] | None:
        """Parse a literal map key: string | identifier (does NOT handle ``$`` prefix)."""
        if (s := self.try_string()) is not None:
            return s
        if (name := self.try_map_identifier()) is not None:
            return name.map(LiteralExpr)
        return None

    def try_map_element(self) -> tuple[Tagged[MapElement], bool] | None:
        """
        Parse one map element; returns ``(element, skip_separator)``.
        ``skip_separator`` is True for ``key :: multiline`` entries.
        """
        self._lexer = self._lexer.skip_whitespace()

        # Splat
        if (ellipsis := self.try_token(TokenType.Ellipsis, mode="key")) is not None:
            expr = self.require_expr()
            return tag(MapSplat(expr=expr.inner()), Span.covering(ellipsis.span, expr.outer())), False

        # For-loop
        if (kw := self.try_map_keyword("for")) is not None:
            binding = self.require_binding()
            self.require_keyword("in")
            iterable = self.require_expr()
            self.require_token(TokenType.Colon)
            inner, skip = self.require_map_element()
            return tag(
                MapLoop(binding=binding, iterable=iterable.inner(), element=inner),
                Span.covering(kw.span, inner.span),
            ), skip

        # When-guard
        if (kw := self.try_map_keyword("when")) is not None:
            condition = self.require_expr()
            self.require_token(TokenType.Colon)
            inner, skip = self.require_map_element()
            span = Span.covering(kw.span, inner.span)
            return tag(MapCond(condition=condition.inner(), element=inner), span), skip

        # Dynamic key: $expr
        if (dollar := self.try_token(TokenType.Dollar, mode="key")) is not None:
            expr = self.require_expr()
            key: Tagged[Expr] = expr.inner()
            elem_start = dollar.span
            self.require_token(TokenType.Colon, mode="key")
            value = self.require_expr()
            span = Span.covering(elem_start, value.outer())
            return tag(MapSingleton(key=key, value=value.inner()), span), False

        # Literal key: string | identifier
        if (lit_key := self.try_map_key()) is None:
            return None
        key = lit_key

        elem_start = key.span
        col = key.span.column

        # :: multiline (no separator needed after)
        if self.try_token(TokenType.DoubleColon, mode="key") is not None:
            try:
                ms_lexer, ms_tok = self._lexer.next_multistring(col)
                self._lexer = ms_lexer
                val_str = _multiline(ms_tok.contents.text)
                value_tagged = tag(LiteralExpr(val_str), ms_tok.span)
            except Error:
                value_tagged = self.missing_expr()
                self.error(self.loc(), SyntaxExpected(TokenType.MultiString).reason())
            span = Span.covering(elem_start, value_tagged.span)
            return tag(MapSingleton(key=key, value=value_tagged), span), True

        # : expr
        self.require_token(TokenType.Colon, mode="key")
        value = self.require_expr()
        return tag(
            MapSingleton(key=key, value=value.inner()), Span.covering(elem_start, value.outer())
        ), False

    def require_map_element(self) -> tuple[Tagged[MapElement], bool]:
        return self.require(
            self.try_map_element,
            lambda: (
                tag(
                    MapSingleton(
                        key=self.missing_expr(),
                        value=self.missing_expr(),
                    ),
                    self.loc(),
                ),
                False,
            ),
            lambda: SyntaxExpected(SyntaxElement.MapElement).reason(),
        )

    def try_map(self) -> Tagged[Expr] | None:
        result = self.try_seplist(
            partial(self.try_token, TokenType.OpenBrace),
            self.try_map_element,
            partial(self.try_token, TokenType.Comma),
            partial(self.try_token, TokenType.CloseBrace),
            SyntaxExpected(TokenType.CloseBrace, SyntaxElement.MapElement).reason(),
            SyntaxExpected(TokenType.Comma, TokenType.CloseBrace).reason(),
            close_tok_type=TokenType.CloseBrace,
        )
        if result is None:
            return None
        open_b, elements, close = result
        return tag(MapExpr(elements), Span.covering(open_b.span, close.span))

    # ── Postfix expressions ───────────────────────────────────────────────────

    def try_postfixable(self) -> Paren[Expr] | None:
        """paren | atomic | identifier | list | map."""
        if (open_p := self.try_token(TokenType.OpenParen)) is not None:
            inner = self.require_expr()
            close_p = self.require_token(TokenType.CloseParen)
            return Paren.parenthesized(inner.inner(), Span.covering(open_p.span, close_p.span))

        if (a := self.try_atomic()) is not None:
            return Paren.naked(a)

        if (ident := self.try_identifier()) is not None:
            return Paren.naked(ident.wrap(IdentifierExpr))

        if (lst := self.try_list()) is not None:
            return Paren.naked(lst)

        if (mp := self.try_map()) is not None:
            return Paren.naked(mp)

        return None

    def try_postfix_transform(self) -> Tagged[Transform] | None:
        # .name  →  index by string literal
        if (dot := self.try_token(TokenType.Dot)) is not None:
            name = self.try_identifier()
            if name is None:
                self.error(self.loc(), SyntaxExpected(SyntaxElement.Identifier).reason())
                key_expr = self.missing_expr()
            else:
                key_expr = name.map(LiteralExpr)
            return tag(
                BinOpTransform(op=tag(EagerOp.Index, dot.span), operand=key_expr),
                Span.covering(dot.span, key_expr.span),
            )

        # [subscript]
        if (open_b := self.try_token(TokenType.OpenBracket)) is not None:
            subscript = self.require_expr()
            close_b = self.require_token(TokenType.CloseBracket)
            op_span = Span.covering(open_b.span, close_b.span)
            return tag(
                BinOpTransform(op=tag(EagerOp.Index, op_span), operand=subscript.inner()),
                op_span,
            )

        # (args...)
        if (open_p := self.try_token(TokenType.OpenParen)) is not None:
            args, close_p = self.require_arg_list()
            call_span = Span.covering(open_p.span, close_p.span)
            return tag(FunCallTransform(args=tag(args, call_span)), call_span)

        return None

    def try_postfixed(self) -> Paren[Expr] | None:
        """postfixable followed by zero or more postfix operators."""
        if (pexpr := self.try_postfixable()) is None:
            return None
        while (transform := self.try_postfix_transform()) is not None:
            span = Span.covering(pexpr.outer(), transform.span)
            expr = TransformedExpr(operand=pexpr.inner(), transform=transform.contents)
            pexpr = Paren.naked(tag(expr, span))
        return pexpr

    def require_arg_list(self) -> tuple[list[Tagged[ArgElement]], Tagged[Token | None]]:
        def try_item() -> tuple[Tagged[ArgElement], bool] | None:
            arg = self.try_function_arg()
            return None if arg is None else (arg, False)

        return self.seplist_inner(
            try_item,
            partial(self.try_token, TokenType.Comma),
            partial(self.try_token, TokenType.CloseParen),
            SyntaxExpected(TokenType.CloseParen, SyntaxElement.ArgElement).reason(),
            SyntaxExpected(TokenType.Comma, TokenType.CloseParen).reason(),
            close_tok_type=TokenType.CloseParen,
        )

    def try_function_arg(self) -> Tagged[ArgElement] | None:
        # Splat
        if (ellipsis := self.try_token(TokenType.Ellipsis)) is not None:
            expr = self.require_expr()
            return tag(ArgSplat(expr=expr.inner()), Span.covering(ellipsis.span, expr.outer()))

        # Keyword arg: name: expr — only when ':' immediately follows the name
        with self._save() as recover:
            if (name := self.try_identifier()) is not None:
                if self.try_token(TokenType.Colon) is not None:
                    expr = self.require_expr()
                    return tag(
                        ArgKeyword(key=name, expr=expr.inner()), Span.covering(name.span, expr.outer())
                    )
                recover()  # not a keyword arg; restore and fall through

        if (expr := self.try_expr()) is None:
            return None
        return tag(ArgSingleton(expr.inner()), expr.outer())

    # ── Operator precedence ───────────────────────────────────────────────────

    def try_power(self) -> Paren[Expr] | None:
        """postfixed (^ prefixed)* — right-associative."""
        if (base := self.try_postfixed()) is None:
            return None
        if (caret := self.try_token(TokenType.Caret)) is None:
            return base
        if (rhs := self.try_prefixed()) is None:
            self.error(self.loc(), SyntaxExpected(SyntaxElement.Operand).reason())
            rhs = self.missing_paren()
        return Paren.naked(
            tag(
                TransformedExpr(
                    operand=base.inner(),
                    transform=BinOpTransform(op=tag(EagerOp.Power, caret.span), operand=rhs.inner()),
                ),
                Span.covering(base.outer(), rhs.outer()),
            )
        )

    def try_prefixed(self) -> Paren[Expr] | None:
        """(unary-op)* power."""
        ops: list[Tagged[UnOp | None]] = []
        while True:
            if (tok := self.try_token(TokenType.Plus)) is not None:
                ops.append(tag(None, tok.span))
            elif (tok := self.try_token(TokenType.Minus)) is not None:
                ops.append(tag(UnOp.ArithmeticalNegate, tok.span))
            elif (tok := self.try_keyword("not")) is not None:
                ops.append(tag(UnOp.LogicalNegate, tok.span))
            else:
                break

        operand = self.try_power()
        if operand is None:
            if ops:
                self.error(self.loc(), SyntaxExpected(SyntaxElement.Operand).reason())
                operand = self.missing_paren()
            else:
                return None

        for op in reversed(ops):
            span = Span.covering(op.span, operand.outer())
            operand = Paren.naked(
                tag(
                    TransformedExpr(operand=operand.inner(), transform=UnOpTransform(op=op)),
                    span,
                )
            )
        return operand

    def try_lbinop(
        self,
        sub: Callable[[], Paren[Expr] | None],
        ops: dict[TokenType | str, BinOp],
    ) -> Paren[Expr] | None:
        """Generic left-associative binary operator level."""
        if (lhs := sub()) is None:
            return None
        while True:
            matched_op: EagerOp | LogicOp | None = None
            op_tok: Tagged[Token] | Tagged[str] | None = None
            for key, op_val in ops.items():
                t = self.try_keyword(key) if isinstance(key, str) else self.try_token(key)
                if t is not None:
                    matched_op, op_tok = op_val, t
                    break
            if op_tok is None or matched_op is None:
                break
            if (rhs := sub()) is None:
                self.error(self.loc(), SyntaxExpected(SyntaxElement.Operand).reason())
                rhs = self.missing_paren()
            lhs = Paren.naked(
                tag(
                    TransformedExpr(
                        operand=lhs.inner(),
                        transform=BinOpTransform(op=tag(matched_op, op_tok.span), operand=rhs.inner()),
                    ),
                    Span.covering(lhs.outer(), rhs.outer()),
                )
            )
        return lhs

    def try_product(self) -> Paren[Expr] | None:
        return self.try_lbinop(
            self.try_prefixed,
            {
                TokenType.Asterisk: EagerOp.Multiply,
                TokenType.DoubleSlash: EagerOp.IntegerDivide,
                TokenType.Slash: EagerOp.Divide,
            },
        )

    def try_sum(self) -> Paren[Expr] | None:
        return self.try_lbinop(
            self.try_product,
            {
                TokenType.Plus: EagerOp.Add,
                TokenType.Minus: EagerOp.Subtract,
            },
        )

    def try_inequality(self) -> Paren[Expr] | None:
        return self.try_lbinop(
            self.try_sum,
            {
                TokenType.LessEq: EagerOp.LessEqual,
                TokenType.Less: EagerOp.Less,
                TokenType.GreaterEq: EagerOp.GreaterEqual,
                TokenType.Greater: EagerOp.Greater,
            },
        )

    def try_equality(self) -> Paren[Expr] | None:
        return self.try_lbinop(
            self.try_inequality,
            {
                TokenType.DoubleEq: EagerOp.Equal,
                TokenType.ExclamEq: EagerOp.NotEqual,
            },
        )

    def try_contains(self) -> Paren[Expr] | None:
        return self.try_lbinop(self.try_equality, {"has": EagerOp.Contains})

    def try_conjunction(self) -> Paren[Expr] | None:
        return self.try_lbinop(self.try_contains, {"and": LogicOp.And})

    def try_disjunction(self) -> Paren[Expr] | None:
        return self.try_lbinop(self.try_conjunction, {"or": LogicOp.Or})

    # ── Composite expressions ─────────────────────────────────────────────────

    def try_let(self) -> Paren[Expr] | None:
        """let binding = expr … in expr"""
        if (first_kw := self.try_keyword("let")) is None:
            return None
        bindings: list[tuple[Tagged[Binding], Tagged[Expr]]] = []
        kw: Tagged[str] | None = first_kw
        while kw is not None:
            b = self.require_binding()
            self.require_token(TokenType.Eq)
            val = self.require_expr()
            bindings.append((b, val.inner()))
            kw = self.try_keyword("let")
        self.require_keyword("in")
        body = self.require_expr()
        return Paren.naked(
            tag(
                LetExpr(bindings=bindings, expression=body.inner()),
                Span.covering(first_kw.span, body.outer()),
            )
        )

    def try_branch(self) -> Paren[Expr] | None:
        """if cond then expr else expr"""
        if (kw := self.try_keyword("if")) is None:
            return None
        cond = self.require_expr()
        self.require_keyword("then")
        true_br = self.require_expr()
        self.require_keyword("else")
        false_br = self.require_expr()
        return Paren.naked(
            tag(
                BranchExpr(
                    condition=cond.inner(),
                    true_branch=true_br.inner(),
                    false_branch=false_br.inner(),
                ),
                Span.covering(kw.span, false_br.outer()),
            )
        )

    def _try_function(self) -> Paren[Expr] | None:
        return self.try_fn_new_style() or self.try_fn_old_kw_style() or self.try_fn_old_pos_style()

    # ── Binding helpers used by function parsers ───────────────────────────────

    def parse_list_binding_terminated(
        self,
        try_close: Callable[[], Tagged[Token] | None],
        close_tok_type: TokenType,
        start_span: Span,
    ) -> tuple[Tagged[ListBinding], Tagged[Token | None]]:
        """
        Parse list-binding elements until ``try_close()`` succeeds or no more
        elements can be parsed.

        ``start_span`` should be the span of the opening delimiter so that the
        returned binding's span covers delimiters on both sides.

        Always returns a close token — real on success, Tagged[None]
        (with error recorded) when the terminator is absent.
        """

        def try_item() -> tuple[Tagged[ListBindingElement], bool] | None:
            el = self.try_list_binding_element()
            return None if el is None else (el, False)

        elements, close = self.seplist_inner(
            try_item,
            lambda: self.try_token(TokenType.Comma),
            try_close,
            SyntaxExpected(SyntaxElement.PosParam, TokenType.CloseParen).reason(),
            SyntaxExpected(TokenType.Comma, TokenType.CloseParen).reason(),
            close_tok_type,
        )
        return tag(ListBinding(elements), Span.covering(start_span, close.span)), close

    def parse_map_binding_terminated(
        self,
        try_close: Callable[[], Tagged[Token] | None],
        close_tok_type: TokenType,
        start_span: Span,
    ) -> tuple[Tagged[MapBinding], Tagged[Token | None]]:
        """Same pattern for map bindings."""

        def try_item() -> tuple[Tagged[MapBindingElement], bool] | None:
            el = self.try_map_binding_element()
            return None if el is None else (el, False)

        elements, close = self.seplist_inner(
            try_item,
            lambda: self.try_token(TokenType.Comma),
            try_close,
            SyntaxExpected(SyntaxElement.KeywordParam, TokenType.CloseParen).reason(),
            SyntaxExpected(TokenType.Comma, TokenType.CloseParen).reason(),
            close_tok_type,
        )
        return tag(MapBinding(elements), Span.covering(start_span, close.span)), close

    # ── Function syntax variants ───────────────────────────────────────────────

    def try_fn_new_style(self) -> Paren[Expr] | None:
        """fn ( pos ; kw ) body  |  fn { kw } body"""
        if (fn_kw := self.try_keyword("fn")) is None:
            return None

        if (open_p := self.try_token(TokenType.OpenParen)) is not None:
            # Positional params, terminated by ) or ;
            pos, term = self.parse_list_binding_terminated(
                lambda: self.try_token(TokenType.CloseParen) or self.try_token(TokenType.SemiColon),
                close_tok_type=TokenType.CloseParen,
                start_span=open_p.span,
            )
            kw: Tagged[MapBinding] | None = None
            missing_close = term.contents is None
            if isinstance(term.contents, Token) and term.contents.text == ";":
                kw, close_p = self.parse_map_binding_terminated(
                    lambda: self.try_token(TokenType.CloseParen),
                    close_tok_type=TokenType.CloseParen,
                    start_span=term.span,
                )
                missing_close = close_p.contents is None
            body = self.missing_paren() if missing_close else self.require_expr()
            return Paren.naked(
                tag(
                    FunctionExpr(positional=pos, keywords=kw, expression=body.inner()),
                    Span.covering(fn_kw.span, body.outer()),
                )
            )

        if (open_b := self.try_token(TokenType.OpenBrace)) is not None:
            # Keyword-only function
            kw, close_b = self.parse_map_binding_terminated(
                lambda: self.try_token(TokenType.CloseBrace),
                close_tok_type=TokenType.CloseBrace,
                start_span=open_b.span,
            )
            missing_close = close_b.contents is None
            body = Paren.naked(self.missing_expr()) if missing_close else self.require_expr()
            empty_pos = tag(ListBinding([]), open_b.span)
            return Paren.naked(
                tag(
                    FunctionExpr(positional=empty_pos, keywords=kw, expression=body.inner()),
                    Span.covering(fn_kw.span, body.outer()),
                )
            )

        self.error(
            self.loc(),
            SyntaxExpected(TokenType.OpenParen, TokenType.OpenBrace).reason(),
        )
        return Paren.naked(
            tag(
                FunctionExpr(
                    positional=tag(ListBinding([]), fn_kw.span),
                    keywords=None,
                    expression=self.missing_expr(),
                ),
                fn_kw.span,
            )
        )

    def try_fn_old_kw_style(self) -> Paren[Expr] | None:
        """{| kw_params |} body  (deprecated syntax)"""
        open_bp = self.try_token(TokenType.OpenBracePipe)
        if open_bp is None:
            return None
        kw, close_bp = self.parse_map_binding_terminated(
            lambda: self.try_token(TokenType.CloseBracePipe),
            close_tok_type=TokenType.CloseBracePipe,
            start_span=open_bp.span,
        )
        missing_close = close_bp.contents is None
        body = self.missing_paren() if missing_close else self.require_expr()
        empty_pos = tag(ListBinding([]), open_bp.span.with_length(1))
        return Paren.naked(
            tag(
                FunctionExpr(positional=empty_pos, keywords=kw, expression=body.inner()),
                Span.covering(open_bp.span, body.outer()),
            )
        )

    def try_fn_old_pos_style(self) -> Paren[Expr] | None:
        """| pos ; kw | body  (deprecated syntax)"""
        open_pipe = self.try_token(TokenType.Pipe)
        if open_pipe is None:
            return None
        pos, term = self.parse_list_binding_terminated(
            lambda: self.try_token(TokenType.Pipe) or self.try_token(TokenType.SemiColon),
            close_tok_type=TokenType.Pipe,
            start_span=open_pipe.span,
        )
        kw: Tagged[MapBinding] | None = None
        missing_close = term.contents is None
        if isinstance(term.contents, Token) and term.contents.text == ";":
            kw, close_pipe = self.parse_map_binding_terminated(
                lambda: self.try_token(TokenType.Pipe),
                close_tok_type=TokenType.Pipe,
                start_span=term.span,
            )
            missing_close = close_pipe.contents is None
        body = self.missing_paren() if missing_close else self.require_expr()
        return Paren.naked(
            tag(
                FunctionExpr(positional=pos, keywords=kw, expression=body.inner()),
                Span.covering(open_pipe.span, body.outer()),
            )
        )

    # ── Top-level expression ───────────────────────────────────────────────────

    def try_expr(self) -> Paren[Expr] | None:
        return self.try_let() or self.try_branch() or self._try_function() or self.try_disjunction()

    def require_expr(self) -> Paren[Expr]:
        return self.require(
            self.try_expr,
            self.missing_paren,
            lambda: SyntaxExpected(SyntaxElement.Expression).reason(),
        )

    # ── Bindings ──────────────────────────────────────────────────────────────

    def try_list_binding_element(self) -> Tagged[ListBindingElement] | None:
        # Slurp: ...name  or  ...
        if (ellipsis := self.try_token(TokenType.Ellipsis)) is not None:
            name = self.try_identifier()
            if name is not None:
                return tag(ListBindingSlurpTo(name=name.contents), Span.covering(ellipsis.span, name.span))
            return tag(ListBindingSlurp(), ellipsis.span)

        b = self.try_binding()
        if b is None:
            return None
        if self.try_token(TokenType.Eq) is not None:
            default = self.require_expr()
            span = Span.covering(b.span, default.outer())
            return tag(ListBindingSingleton(binding=b, default=default.inner()), span)
        return tag(ListBindingSingleton(binding=b, default=None), b.span)

    def try_map_binding_element(self) -> Tagged[MapBindingElement] | None:
        # Named slurp: ...name
        if (ellipsis := self.try_token(TokenType.Ellipsis)) is not None:
            name = self.try_identifier()
            if name is None:
                self.error(self.loc(), SyntaxExpected(SyntaxElement.Identifier).reason())
                return tag(MapBindingSlurpTo(name="_"), ellipsis.span)
            return tag(MapBindingSlurpTo(name=name.contents), Span.covering(ellipsis.span, name.span))

        # name (as binding)? (= default)?
        name = self.try_identifier()
        if name is None:
            return None

        sub_binding: Tagged[Binding] | None = None
        if self.try_keyword("as") is not None:
            sub_binding = self.require_binding()

        default: Paren[Expr] | None = None
        if self.try_token(TokenType.Eq) is not None:
            default = self.require_expr()

        if sub_binding is None:
            sub_binding = tag(IdentifierBinding(name=name), name.span)

        end = default.outer() if default is not None else sub_binding.span
        default_inner = default.inner() if default is not None else None
        return tag(
            MapBindingSingleton(key=name, binding=sub_binding, default=default_inner),
            Span.covering(name.span, end),
        )

    def try_binding(self) -> Tagged[Binding] | None:
        # Identifier
        name = self.try_identifier()
        if name is not None:
            return tag(IdentifierBinding(name=name), name.span)

        # List pattern: [ ... ]
        if (open_b := self.try_token(TokenType.OpenBracket)) is not None:
            lb, close = self.parse_list_binding_terminated(
                lambda: self.try_token(TokenType.CloseBracket),
                close_tok_type=TokenType.CloseBracket,
                start_span=open_b.span,
            )
            return tag(ListPatternBinding(binding=lb), Span.covering(open_b.span, close.span))

        # Map pattern: { ... }
        if (open_b := self.try_token(TokenType.OpenBrace)) is not None:
            mb, close = self.parse_map_binding_terminated(
                lambda: self.try_token(TokenType.CloseBrace),
                close_tok_type=TokenType.CloseBrace,
                start_span=open_b.span,
            )
            return tag(MapPatternBinding(binding=mb), Span.covering(open_b.span, close.span))

        return None

    def require_binding(self) -> Tagged[Binding]:
        return self.require(
            self.try_binding,
            self.missing_binding,
            lambda: SyntaxExpected(SyntaxElement.Binding).reason(),
        )

    # ── Top-level statements ───────────────────────────────────────────────────

    def try_import(self) -> ImportStatement | None:
        """import "path" as binding"""
        if self.try_keyword("import") is None:
            return None
        open_q = self.require_token(TokenType.DoubleQuote)
        path_str = self.try_raw_string_content()
        close_q = self.require_token(TokenType.DoubleQuote, mode="string")
        path: Tagged[str] = tag(path_str or "", Span.covering(open_q.span, close_q.span))
        self.require_keyword("as")
        binding = self.require_binding()
        return ImportStatement(path=path, binding=binding)

    def parse_file(self) -> File:
        """Parse a complete Gold file: imports* expression."""
        statements: list[TopLevel] = []
        while True:
            stmt = self.try_import()
            if stmt is None:
                break
            statements.append(stmt)

        pexpr = self.require_expr()

        if not self.at_eof():
            pos = self._lexer.skip_whitespace().position
            self.error(pos.with_length(0), SyntaxExpected(SyntaxElement.EndOfInput).reason())

        return File(statements=statements, expression=pexpr.inner())


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
