from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from functools import partial
from typing import TYPE_CHECKING


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
    TransformedExpr,
    UnOp,
    UnOpTransform,
)
from .error import (
    Action,
    AnySyntaxElement,
    Error,
    Reason,
    ReasonSyntax,
    SyntaxElement,
    SyntaxElementToken,
    SyntaxExpected,
    SyntaxUnexpectedEof,
)
from .lexer import Lexer, Token, TokenType
from .pprint import pprint_parse_result
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

    def pprint(self, *, show_spans: bool = True, max_str_len: int | None = None) -> str:
        return pprint_parse_result(self, show_spans=show_spans, max_str_len=max_str_len)

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

    def _error(self, span: Span, reason: Reason) -> None:
        self._errors.append(Error.new(reason).tag(span, Action.Parse))

    def _here(self) -> Span:
        return self._lexer.position.with_length(0)

    def _missing_expr(self) -> Tagged[Expr]:
        """Sentinel for a required expression that could not be parsed."""
        return tag(MissingExpr(), self._here())

    def _missing_paren(self) -> Paren[Expr]:
        return Paren.naked(self._missing_expr())

    def _missing_binding(self) -> Tagged[Binding]:
        return tag(MissingBinding(), self._here())

    def _at_eof(self) -> bool:
        """Return True if there is no more non-whitespace input."""
        try:
            self._lexer.next_token()
            return False
        except Error as e:
            return isinstance(e.reason, ReasonSyntax) and isinstance(e.reason.syntax, SyntaxUnexpectedEof)

    def _require[T](
        self,
        parser: Callable[[], T | None],
        fallback: Callable[[], T],
        reason: Callable[[], Reason],
    ) -> T:
        result = parser()
        if result is None:
            self._error(self._here(), reason())
            return fallback()
        return result

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
        except Error:
            return None

    def _require_tok(self, kind: TokenType, mode: str = "default") -> Tagged[Token | None]:
        """Consume a required token; record error and return dummy if missing."""
        return self._require(
            partial(self._try_tok, kind, mode),
            lambda: tag(None, self._here()),
            lambda: ReasonSyntax(SyntaxExpected(SyntaxElementToken(kind))),
        )

    def _try_keyword(self, kw: str) -> Tagged[str] | None:
        try:
            lexer, tok = self._lexer.next_token()
            if tok.contents.kind == TokenType.Name and tok.contents.text == kw:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except Error:
            return None

    def _try_map_keyword(self, kw: str) -> Tagged[str] | None:
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

    def _require_keyword(self, kw: str) -> Tagged[str]:
        return self._require(
            partial(self._try_keyword, kw),
            lambda: tag(kw, self._here()),
            lambda: ReasonSyntax(SyntaxExpected(self._KW_ELEMENTS.get(kw, SyntaxElement.Expression))),
        )

    def _try_identifier(self) -> Tagged[str] | None:
        """A Name token that is not a reserved keyword."""
        try:
            lexer, tok = self._lexer.next_token()
            if tok.contents.kind == TokenType.Name and tok.contents.text not in KEYWORDS:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except Error:
            return None

    def _try_map_identifier(self) -> Tagged[str] | None:
        """Any Name token in map-key context (no keyword restriction)."""
        try:
            lexer, tok = self._lexer.next_key()
            if tok.contents.kind == TokenType.Name:
                self._lexer = lexer
                return tok.map(lambda t: t.text)
            return None
        except Error:
            return None

    # ── fmtspec helpers ────────────────────────────────────────────────────────

    def _fmtspec_try_char(self) -> str | None:
        try:
            lexer, tok = self._lexer.next_fmtspec()
            if tok.contents.kind == TokenType.Char:
                self._lexer = lexer
                return tok.contents.text
            return None
        except Error:
            return None

    def _fmtspec_try_number(self) -> int | None:
        try:
            lexer, tok = self._lexer.next_fmtspec()
            if tok.contents.kind == TokenType.Integer:
                self._lexer = lexer
                return int(tok.contents.text)
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

    def _require_format_spec(self) -> FormatSpec:
        """Parse a format-spec token stream (used after ':' in string interpolation)."""
        # fill + align: try (any-char, align-char) first, then just (align-char)
        saved = self._lexer
        fill_char: str | None = None
        align: AlignSpec | None = None

        with self._save() as recover:
            if (c1 := self._fmtspec_try_char()) is not None:
                if (c2 := self._fmtspec_try_char()) in self._ALIGN_CHARS:
                    fill_char, align = c1, self._ALIGN_CHARS[c2]
                else:
                    # c1 might itself be an alignment character
                    recover()
                    # self._lexer = saved
                    c = self._fmtspec_try_char()
                    if c is not None and c in self._ALIGN_CHARS:
                        align = self._ALIGN_CHARS[c]
                    else:
                        recover()
                        self._lexer = saved  # nothing matched

        # sign: + - <space>
        with self._save() as recover:
            c = self._fmtspec_try_char()
            _sign_map = {"+": SignSpec.Plus, "-": SignSpec.Minus, " ": SignSpec.Space}
            sign: SignSpec | None = _sign_map.get(c or "")
            if sign is None:
                recover()

        # alternate: #
        with self._save() as recover:
            if not (alternate := self._fmtspec_try_char() == "#"):
                recover()

        # zero-fill shorthand: 0 (sets fill='0', align=AfterSign when no explicit fill/align)
        with self._save() as recover:
            if not (zero := self._fmtspec_try_char() == "0"):
                recover()

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

    def _try_raw_string_content(self) -> str | None:
        """Consume a StringLit token and decode its escape sequences."""
        if (tok := self._try_tok(TokenType.StringLit, mode="string")) is None:
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

    def _try_tring_interp(self) -> StringElement | None:
        """Parse ``${ expr }`` or ``${ expr : fmtspec }``."""
        if self._try_tok(TokenType.Dollar, mode="string") is None:
            return None
        self._require_tok(TokenType.OpenBrace)
        expr = self._require_expr()
        fmt: FormatSpec | None = None
        if self._try_tok(TokenType.Colon) is not None:
            fmt = self._require_format_spec()
            self._require_tok(TokenType.CloseBrace, mode="fmtspec")
        else:
            self._require_tok(TokenType.CloseBrace)
        return StringInterpolate(expr=expr.inner(), fmt=fmt)

    def _try_string_part(self) -> Tagged[list[StringElement]] | None:
        """Parse one ``"..."`` string part; returns elements tagged with outer span."""
        open_q = self._try_tok(TokenType.DoubleQuote)
        if open_q is None:
            return None
        elements: list[StringElement] = []
        while True:
            if (interp := self._try_tring_interp()) is not None:
                elements.append(interp)
                continue
            if (raw := self._try_raw_string_content()) is not None:
                elements.append(StringRaw(raw))
                continue
            break
        close_q = self._require_tok(TokenType.DoubleQuote, mode="string")
        span = Span.covering(open_q.span, close_q.span)
        return tag(elements, span)

    def _try_string(self) -> Tagged[Expr] | None:
        """Parse one or more adjacent string parts (adjacent strings are concatenated)."""
        first = self._try_string_part()
        if first is None:
            return None
        all_elements: list[StringElement] = list(first.contents)
        last_span = first.span
        while True:
            if (more := self._try_string_part()) is None:
                break
            all_elements.extend(more.contents)
            last_span = more.span
        span = Span.covering(first.span, last_span)
        return self._make_string_expr(all_elements, span)

    @staticmethod
    def _make_string_expr(elements: list[StringElement], span: Span) -> Tagged[Expr]:
        if not elements:
            return tag(LiteralExpr(""), span)
        if len(elements) == 1 and isinstance(elements[0], StringRaw):
            return tag(LiteralExpr(elements[0].value), span)
        return tag(StringExpr(elements), span)

    # ── Numbers / atomics ─────────────────────────────────────────────────────

    def _try_number(self) -> Tagged[Expr] | None:
        if (tok := self._try_tok(TokenType.Float)) is not None:
            try:
                return tok.map(lambda t: LiteralExpr(float(t.text.replace("_", ""))))
            except ValueError:
                pass
        if (tok := self._try_tok(TokenType.Integer)) is not None:
            try:
                return tok.map(lambda t: LiteralExpr(int(t.text.replace("_", ""))))
            except ValueError:
                pass
        return None

    def _try_atomic(self) -> Tagged[Expr] | None:
        """null | true | false | number | string."""
        for kw, val in (("null", None), ("true", True), ("false", False)):
            if (tok := self._try_keyword(kw)) is not None:
                return tok.map(lambda _: LiteralExpr(val))
        if (n := self._try_number()) is not None:
            return n
        if (s := self._try_string()) is not None:
            return s
        return None

    # ── Separated-list kernel ─────────────────────────────────────────────────

    def _seplist_inner[T](
        self,
        try_item: Callable[[], tuple[T, bool] | None],
        try_sep: Callable[[], Tagged[Token] | None],
        try_close: Callable[[], Tagged[Token] | None],
        err_missing_item: Reason | None,
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
        close: Tagged[Token | None] | None = None
        need_sep = False

        while True:
            if not need_sep:
                if (close := try_close()) is not None:
                    break
                if (result := try_item()) is None:
                    if err_missing_item is not None:
                        self._error(self._here(), err_missing_item)
                        if (close := try_close()) is None:
                            close = tag(None, self._here())
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
                sep_pos = self._here()
                saved = self._lexer
                if (result := try_item()) is None:
                    self._lexer = saved  # restore; break silently
                    break
                self._error(sep_pos, err_missing_sep)
                item, skip = result
                items.append(item)
                need_sep = not skip

        if close is None:
            close = self._require_tok(close_tok_type)
        return items, close

    def _seplist[T](
        self,
        try_open: Callable[[], Tagged | None],
        try_item: Callable[[], tuple[T, bool] | None],
        try_sep: Callable[[], Tagged[Token] | None],
        try_close: Callable[[], Tagged[Token] | None],
        err_missing_item: Reason | None,
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
        items, close_tok = self._seplist_inner(
            try_item, try_sep, try_close, err_missing_item, err_missing_sep, close_tok_type
        )
        return open_tok, items, close_tok

    # ── List ──────────────────────────────────────────────────────────────────

    def _try_list_element(self) -> Paren[ListElement] | None:
        # Splat
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            expr = self._require_expr()
            return Paren.naked(tag(ListSplat(expr=expr.inner()), Span.covering(ellipsis.span, expr.outer())))

        # For-loop: for binding in iterable : element
        if (kw := self._try_keyword("for")) is not None:
            binding = self._require_binding()
            self._require_keyword("in")
            iterable = self._require_expr()
            self._require_tok(TokenType.Colon)
            element = self._require_list_element()
            return Paren.naked(
                tag(
                    ListLoop(binding=binding, iterable=iterable.inner(), element=element.inner()),
                    Span.covering(kw.span, element.outer()),
                )
            )

        # When-guard: when expr : element
        if (kw := self._try_keyword("when")) is not None:
            condition = self._require_expr()
            self._require_tok(TokenType.Colon)
            element = self._require_list_element()
            return Paren.naked(
                tag(
                    ListCond(condition=condition.inner(), element=element.inner()),
                    Span.covering(kw.span, element.outer()),
                )
            )

        # Singleton
        expr = self._try_expr()
        if expr is None:
            return None
        return expr.map_wrap(ListSingleton)

    def _require_list_element(self) -> Paren[ListElement]:
        return self._require(
            self._try_list_element,
            lambda: Paren.naked(tag(ListSingleton(self._missing_expr()), self._here())),
            lambda: ReasonSyntax(SyntaxExpected(SyntaxElement.ListElement)),
        )

    def _try_list(self) -> Tagged[Expr] | None:
        def try_item() -> tuple[Tagged[ListElement], bool] | None:
            el = self._try_list_element()
            return None if el is None else (el.inner(), False)

        result = self._seplist(
            partial(self._try_tok, TokenType.OpenBracket),
            try_item,
            partial(self._try_tok, TokenType.Comma),
            partial(self._try_tok, TokenType.CloseBracket),
            ReasonSyntax(
                SyntaxExpected(SyntaxElementToken(TokenType.CloseBracket), SyntaxElement.ListElement)
            ),
            ReasonSyntax(
                SyntaxExpected(
                    SyntaxElementToken(TokenType.Comma),
                    SyntaxElementToken(TokenType.CloseBracket),
                )
            ),
            close_tok_type=TokenType.CloseBracket,
        )
        if result is None:
            return None
        open_b, elements, close = result
        return tag(ListExpr(elements), Span.covering(open_b.span, close.span))

    # ── Map ───────────────────────────────────────────────────────────────────

    def _try_map_key(self) -> Tagged[Expr] | None:
        """Parse a literal map key: string | identifier (does NOT handle ``$`` prefix)."""
        if (s := self._try_string()) is not None:
            return s
        if (name := self._try_map_identifier()) is not None:
            return name.map(LiteralExpr)
        return None

    def _try_map_element(self) -> tuple[Tagged[MapElement], bool] | None:
        """
        Parse one map element; returns ``(element, skip_separator)``.
        ``skip_separator`` is True for ``key :: multiline`` entries.
        """
        self._lexer = self._lexer.skip_whitespace()

        # Splat
        if (ellipsis := self._try_tok(TokenType.Ellipsis, mode="key")) is not None:
            expr = self._require_expr()
            return tag(MapSplat(expr=expr.inner()), Span.covering(ellipsis.span, expr.outer())), False

        # For-loop
        if (kw := self._try_map_keyword("for")) is not None:
            binding = self._require_binding()
            self._require_keyword("in")
            iterable = self._require_expr()
            self._require_tok(TokenType.Colon)
            inner, skip = self._require_map_element()
            return tag(
                MapLoop(binding=binding, iterable=iterable.inner(), element=inner),
                Span.covering(kw.span, inner.span),
            ), skip

        # When-guard
        if (kw := self._try_map_keyword("when")) is not None:
            condition = self._require_expr()
            self._require_tok(TokenType.Colon)
            inner, skip = self._require_map_element()
            span = Span.covering(kw.span, inner.span)
            return tag(MapCond(condition=condition.inner(), element=inner), span), skip

        # Dynamic key: $expr
        if (dollar := self._try_tok(TokenType.Dollar, mode="key")) is not None:
            if (expr := self._try_expr()) is None:
                self._error(self._here(), ReasonSyntax(SyntaxExpected(SyntaxElement.Expression)))
                return tag(
                    MapSingleton(key=self._missing_expr(), value=self._missing_expr()), dollar.span
                ), False
            key: Tagged[Expr] = expr.inner()
            elem_start = dollar.span
            self._require_tok(TokenType.Colon, mode="key")
            value = self._require_expr()
            span = Span.covering(elem_start, value.outer())
            return tag(MapSingleton(key=key, value=value.inner()), span), False

        # Literal key: string | identifier
        if (lit_key := self._try_map_key()) is None:
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
                value_tagged = tag(LiteralExpr(val_str), ms_tok.span)
            except Error:
                value_tagged = self._missing_expr()
                self._error(
                    self._here(), ReasonSyntax(SyntaxExpected(SyntaxElementToken(TokenType.MultiString)))
                )
            span = Span.covering(elem_start, value_tagged.span)
            return tag(MapSingleton(key=key, value=value_tagged), span), True

        # : expr
        self._require_tok(TokenType.Colon, mode="key")
        value = self._require_expr()
        return tag(
            MapSingleton(key=key, value=value.inner()), Span.covering(elem_start, value.outer())
        ), False

    def _require_map_element(self) -> tuple[Tagged[MapElement], bool]:
        return self._require(
            self._try_map_element,
            lambda: (
                tag(
                    MapSingleton(
                        key=self._missing_expr(),
                        value=self._missing_expr(),
                    ),
                    self._here(),
                ),
                False,
            ),
            lambda: ReasonSyntax(SyntaxExpected(SyntaxElement.MapElement)),
        )

    def _try_map(self) -> Tagged[Expr] | None:
        result = self._seplist(
            partial(self._try_tok, TokenType.OpenBrace),
            self._try_map_element,
            partial(self._try_tok, TokenType.Comma),
            partial(self._try_tok, TokenType.CloseBrace),
            ReasonSyntax(SyntaxExpected(SyntaxElementToken(TokenType.CloseBrace), SyntaxElement.MapElement)),
            ReasonSyntax(
                SyntaxExpected(
                    SyntaxElementToken(TokenType.Comma),
                    SyntaxElementToken(TokenType.CloseBrace),
                )
            ),
            close_tok_type=TokenType.CloseBrace,
        )
        if result is None:
            return None
        open_b, elements, close = result
        return tag(MapExpr(elements), Span.covering(open_b.span, close.span))

    # ── Postfix expressions ───────────────────────────────────────────────────

    def _try_postfixable(self) -> Paren[Expr] | None:
        """paren | atomic | identifier | list | map."""
        if (open_p := self._try_tok(TokenType.OpenParen)) is not None:
            inner = self._require_expr()
            close_p = self._require_tok(TokenType.CloseParen)
            return Paren.parenthesized(inner.inner(), Span.covering(open_p.span, close_p.span))

        if (a := self._try_atomic()) is not None:
            return Paren.naked(a)

        if (ident := self._try_identifier()) is not None:
            return Paren.naked(ident.wrap(IdentifierExpr))

        if (lst := self._try_list()) is not None:
            return Paren.naked(lst)

        if (mp := self._try_map()) is not None:
            return Paren.naked(mp)

        return None

    def _try_postfixed(self) -> Paren[Expr] | None:
        """postfixable followed by zero or more postfix operators."""
        if (pexpr := self._try_postfixable()) is None:
            return None

        while True:
            # .name  →  index by string literal
            if (dot := self._try_tok(TokenType.Dot)) is not None:
                name = self._try_identifier()
                if name is None:
                    self._error(self._here(), ReasonSyntax(SyntaxExpected(SyntaxElement.Identifier)))
                    key_expr = self._missing_expr()
                else:
                    key_expr = name.map(LiteralExpr)
                span = Span.covering(pexpr.outer(), key_expr.span)
                pexpr = Paren.naked(
                    tag(
                        TransformedExpr(
                            operand=pexpr.inner(),
                            transform=BinOpTransform(op=tag(EagerOp.Index, dot.span), operand=key_expr),
                        ),
                        span,
                    )
                )
                continue

            # [subscript]
            if (open_b := self._try_tok(TokenType.OpenBracket)) is not None:
                subscript = self._require_expr()
                close_b = self._require_tok(TokenType.CloseBracket)
                op_span = Span.covering(open_b.span, close_b.span)
                pexpr = Paren.naked(
                    tag(
                        TransformedExpr(
                            operand=pexpr.inner(),
                            transform=BinOpTransform(
                                op=tag(EagerOp.Index, op_span), operand=subscript.inner()
                            ),
                        ),
                        Span.covering(pexpr.outer(), close_b.span),
                    )
                )
                continue

            # (args...)
            if (open_p := self._try_tok(TokenType.OpenParen)) is not None:
                args, close_p = self._require_arg_list()
                call_span = Span.covering(open_p.span, close_p.span)
                pexpr = Paren.naked(
                    tag(
                        TransformedExpr(
                            operand=pexpr.inner(),
                            transform=FunCallTransform(args=tag(args, call_span)),
                        ),
                        Span.covering(pexpr.outer(), close_p.span),
                    )
                )
                continue

            break
        return pexpr

    def _require_arg_list(self) -> tuple[list[Tagged[ArgElement]], Tagged[Token | None]]:
        def try_item() -> tuple[Tagged[ArgElement], bool] | None:
            arg = self._try_function_arg()
            return None if arg is None else (arg, False)

        return self._seplist_inner(
            try_item,
            partial(self._try_tok, TokenType.Comma),
            partial(self._try_tok, TokenType.CloseParen),
            ReasonSyntax(SyntaxExpected(SyntaxElementToken(TokenType.CloseParen), SyntaxElement.ArgElement)),
            ReasonSyntax(
                SyntaxExpected(
                    SyntaxElementToken(TokenType.Comma),
                    SyntaxElementToken(TokenType.CloseParen),
                )
            ),
            close_tok_type=TokenType.CloseParen,
        )

    def _try_function_arg(self) -> Tagged[ArgElement] | None:
        # Splat
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            expr = self._require_expr()
            return tag(ArgSplat(expr=expr.inner()), Span.covering(ellipsis.span, expr.outer()))

        # Keyword arg: name: expr — only when ':' immediately follows the name
        with self._save() as recover:
            if (name := self._try_identifier()) is not None:
                if self._try_tok(TokenType.Colon) is not None:
                    expr = self._require_expr()
                    return tag(
                        ArgKeyword(key=name, expr=expr.inner()), Span.covering(name.span, expr.outer())
                    )
                recover()  # not a keyword arg; restore and fall through

        if (expr := self._try_expr()) is None:
            return None
        return tag(ArgSingleton(expr.inner()), expr.outer())

    # ── Operator precedence ───────────────────────────────────────────────────

    def _try_power(self) -> Paren[Expr] | None:
        """postfixed (^ prefixed)* — right-associative."""
        if (base := self._try_postfixed()) is None:
            return None
        if (caret := self._try_tok(TokenType.Caret)) is None:
            return base
        if (rhs := self._try_prefixed()) is None:
            self._error(self._here(), ReasonSyntax(SyntaxExpected(SyntaxElement.Operand)))
            rhs = self._missing_paren()
        return Paren.naked(
            tag(
                TransformedExpr(
                    operand=base.inner(),
                    transform=BinOpTransform(op=tag(EagerOp.Power, caret.span), operand=rhs.inner()),
                ),
                Span.covering(base.outer(), rhs.outer()),
            )
        )

    def _try_prefixed(self) -> Paren[Expr] | None:
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
                self._error(self._here(), ReasonSyntax(SyntaxExpected(SyntaxElement.Operand)))
                operand = self._missing_paren()
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

    def _try_lbinop(
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
                t = self._try_keyword(key) if isinstance(key, str) else self._try_tok(key)
                if t is not None:
                    matched_op, op_tok = op_val, t
                    break
            if op_tok is None or matched_op is None:
                break
            if (rhs := sub()) is None:
                self._error(self._here(), ReasonSyntax(SyntaxExpected(SyntaxElement.Operand)))
                rhs = self._missing_paren()
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

    def _try_product(self) -> Paren[Expr] | None:
        return self._try_lbinop(
            self._try_prefixed,
            {
                TokenType.Asterisk: EagerOp.Multiply,
                TokenType.DoubleSlash: EagerOp.IntegerDivide,
                TokenType.Slash: EagerOp.Divide,
            },
        )

    def _try_sum(self) -> Paren[Expr] | None:
        return self._try_lbinop(
            self._try_product,
            {
                TokenType.Plus: EagerOp.Add,
                TokenType.Minus: EagerOp.Subtract,
            },
        )

    def _try_inequality(self) -> Paren[Expr] | None:
        return self._try_lbinop(
            self._try_sum,
            {
                TokenType.LessEq: EagerOp.LessEqual,
                TokenType.Less: EagerOp.Less,
                TokenType.GreaterEq: EagerOp.GreaterEqual,
                TokenType.Greater: EagerOp.Greater,
            },
        )

    def _try_equality(self) -> Paren[Expr] | None:
        return self._try_lbinop(
            self._try_inequality,
            {
                TokenType.DoubleEq: EagerOp.Equal,
                TokenType.ExclamEq: EagerOp.NotEqual,
            },
        )

    def _try_contains(self) -> Paren[Expr] | None:
        return self._try_lbinop(self._try_equality, {"has": EagerOp.Contains})

    def _try_conjunction(self) -> Paren[Expr] | None:
        return self._try_lbinop(self._try_contains, {"and": LogicOp.And})

    def _try_disjunction(self) -> Paren[Expr] | None:
        return self._try_lbinop(self._try_conjunction, {"or": LogicOp.Or})

    # ── Composite expressions ─────────────────────────────────────────────────

    def _try_let(self) -> Paren[Expr] | None:
        """let binding = expr … in expr"""
        if (first_kw := self._try_keyword("let")) is None:
            return None
        bindings: list[tuple[Tagged[Binding], Tagged[Expr]]] = []
        kw: Tagged[str] | None = first_kw
        while kw is not None:
            b = self._require_binding()
            self._require_tok(TokenType.Eq)
            val = self._require_expr()
            bindings.append((b, val.inner()))
            kw = self._try_keyword("let")
        self._require_keyword("in")
        body = self._require_expr()
        return Paren.naked(
            tag(
                LetExpr(bindings=bindings, expression=body.inner()),
                Span.covering(first_kw.span, body.outer()),
            )
        )

    def _try_branch(self) -> Paren[Expr] | None:
        """if cond then expr else expr"""
        if (kw := self._try_keyword("if")) is None:
            return None
        cond = self._require_expr()
        self._require_keyword("then")
        true_br = self._require_expr()
        self._require_keyword("else")
        false_br = self._require_expr()
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
        return self._try_fn_new_style() or self._try_fn_old_kw_style() or self._try_fn_old_pos_style()

    # ── Binding helpers used by function parsers ───────────────────────────────

    def _parse_list_binding_terminated(
        self,
        try_close: Callable[[], Tagged[Token] | None],
        close_tok_type: TokenType,
        start_span: Span | None = None,
    ) -> tuple[Tagged[ListBinding], Tagged[Token | None]]:
        """
        Parse list-binding elements until ``try_close()`` succeeds or no more
        elements can be parsed.

        ``start_span`` should be the span of the opening delimiter so that the
        returned binding's span covers delimiters on both sides.

        Always returns a close token — real on success, Tagged[None]
        (with error recorded) when the terminator is absent.
        """
        inner_start = self._here()

        def try_item() -> tuple[Tagged[ListBindingElement], bool] | None:
            el = self._try_list_binding_element()
            return None if el is None else (el, False)

        elements, close = self._seplist_inner(
            try_item,
            lambda: self._try_tok(TokenType.Comma),
            try_close,
            ReasonSyntax(SyntaxExpected(SyntaxElement.PosParam, SyntaxElementToken(TokenType.CloseParen))),
            ReasonSyntax(
                SyntaxExpected(SyntaxElementToken(TokenType.Comma), SyntaxElementToken(TokenType.CloseParen))
            ),
            close_tok_type,
        )
        actual_start = start_span if start_span is not None else inner_start
        return tag(ListBinding(elements), Span.covering(actual_start, close.span)), close

    def _parse_map_binding_terminated(
        self,
        try_close: Callable[[], Tagged[Token] | None],
        close_tok_type: TokenType,
        start_span: Span | None = None,
    ) -> tuple[Tagged[MapBinding], Tagged[Token | None]]:
        """Same pattern for map bindings."""
        inner_start = self._here()

        def try_item() -> tuple[Tagged[MapBindingElement], bool] | None:
            el = self._try_map_binding_element()
            return None if el is None else (el, False)

        elements, close = self._seplist_inner(
            try_item,
            lambda: self._try_tok(TokenType.Comma),
            try_close,
            ReasonSyntax(
                SyntaxExpected(SyntaxElement.KeywordParam, SyntaxElementToken(TokenType.CloseParen))
            ),
            ReasonSyntax(
                SyntaxExpected(SyntaxElementToken(TokenType.Comma), SyntaxElementToken(TokenType.CloseParen))
            ),
            close_tok_type,
        )
        actual_start = start_span if start_span is not None else inner_start
        return tag(MapBinding(elements), Span.covering(actual_start, close.span)), close

    # ── Function syntax variants ───────────────────────────────────────────────

    def _try_fn_new_style(self) -> Paren[Expr] | None:
        """fn ( pos ; kw ) body  |  fn { kw } body"""
        if (fn_kw := self._try_keyword("fn")) is None:
            return None

        if (open_p := self._try_tok(TokenType.OpenParen)) is not None:
            # Positional params, terminated by ) or ;
            pos, term = self._parse_list_binding_terminated(
                lambda: self._try_tok(TokenType.CloseParen) or self._try_tok(TokenType.SemiColon),
                close_tok_type=TokenType.CloseParen,
                start_span=open_p.span,
            )
            kw: Tagged[MapBinding] | None = None
            missing_close = term.contents is None
            if isinstance(term.contents, Token) and term.contents.text == ";":
                kw, close_p = self._parse_map_binding_terminated(
                    lambda: self._try_tok(TokenType.CloseParen),
                    close_tok_type=TokenType.CloseParen,
                    start_span=term.span,
                )
                missing_close = close_p.contents is None
            body = Paren.naked(self._missing_expr()) if missing_close else self._require_expr()
            return Paren.naked(
                tag(
                    FunctionExpr(positional=pos, keywords=kw, expression=body.inner()),
                    Span.covering(fn_kw.span, body.outer()),
                )
            )

        if (open_b := self._try_tok(TokenType.OpenBrace)) is not None:
            # Keyword-only function
            kw, close_b = self._parse_map_binding_terminated(
                lambda: self._try_tok(TokenType.CloseBrace),
                close_tok_type=TokenType.CloseBrace,
                start_span=open_b.span,
            )
            missing_close = close_b.contents is None
            body = Paren.naked(self._missing_expr()) if missing_close else self._require_expr()
            empty_pos = tag(ListBinding([]), open_b.span)
            return Paren.naked(
                tag(
                    FunctionExpr(positional=empty_pos, keywords=kw, expression=body.inner()),
                    Span.covering(fn_kw.span, body.outer()),
                )
            )

        self._error(
            self._here(),
            ReasonSyntax(
                SyntaxExpected(
                    SyntaxElementToken(TokenType.OpenParen), SyntaxElementToken(TokenType.OpenBrace)
                )
            ),
        )
        return Paren.naked(
            tag(
                FunctionExpr(
                    positional=tag(ListBinding([]), fn_kw.span),
                    keywords=None,
                    expression=self._missing_expr(),
                ),
                fn_kw.span,
            )
        )

    def _try_fn_old_kw_style(self) -> Paren[Expr] | None:
        """{| kw_params |} body  (deprecated syntax)"""
        open_bp = self._try_tok(TokenType.OpenBracePipe)
        if open_bp is None:
            return None
        kw, close_bp = self._parse_map_binding_terminated(
            lambda: self._try_tok(TokenType.CloseBracePipe),
            close_tok_type=TokenType.CloseBracePipe,
            start_span=open_bp.span,
        )
        missing_close = close_bp.contents is None
        body = Paren.naked(self._missing_expr()) if missing_close else self._require_expr()
        empty_pos = tag(ListBinding([]), open_bp.span.with_length(1))
        return Paren.naked(
            tag(
                FunctionExpr(positional=empty_pos, keywords=kw, expression=body.inner()),
                Span.covering(open_bp.span, body.outer()),
            )
        )

    def _try_fn_old_pos_style(self) -> Paren[Expr] | None:
        """| pos ; kw | body  (deprecated syntax)"""
        open_pipe = self._try_tok(TokenType.Pipe)
        if open_pipe is None:
            return None
        pos, term = self._parse_list_binding_terminated(
            lambda: self._try_tok(TokenType.Pipe) or self._try_tok(TokenType.SemiColon),
            close_tok_type=TokenType.Pipe,
            start_span=open_pipe.span,
        )
        kw: Tagged[MapBinding] | None = None
        missing_close = term.contents is None
        if isinstance(term.contents, Token) and term.contents.text == ";":
            kw, close_pipe = self._parse_map_binding_terminated(
                lambda: self._try_tok(TokenType.Pipe),
                close_tok_type=TokenType.Pipe,
                start_span=term.span,
            )
            missing_close = close_pipe.contents is None
        body = Paren.naked(self._missing_expr()) if missing_close else self._require_expr()
        return Paren.naked(
            tag(
                FunctionExpr(positional=pos, keywords=kw, expression=body.inner()),
                Span.covering(open_pipe.span, body.outer()),
            )
        )

    # ── Top-level expression ───────────────────────────────────────────────────

    def _try_expr(self) -> Paren[Expr] | None:
        return self._try_let() or self._try_branch() or self._try_function() or self._try_disjunction()

    def _require_expr(self) -> Paren[Expr]:
        expr = self._try_expr()
        if expr is not None:
            return expr
        sp = self._here()
        self._error(sp, ReasonSyntax(SyntaxExpected(SyntaxElement.Expression)))
        return self._missing_paren()

    # ── Bindings ──────────────────────────────────────────────────────────────

    def _try_list_binding_element(self) -> Tagged[ListBindingElement] | None:
        # Slurp: ...name  or  ...
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            name = self._try_identifier()
            if name is not None:
                return tag(ListBindingSlurpTo(name=name.contents), Span.covering(ellipsis.span, name.span))
            return tag(ListBindingSlurp(), ellipsis.span)

        b = self._try_binding()
        if b is None:
            return None
        if self._try_tok(TokenType.Eq) is not None:
            default = self._require_expr()
            span = Span.covering(b.span, default.outer())
            return tag(ListBindingSingleton(binding=b, default=default.inner()), span)
        return tag(ListBindingSingleton(binding=b, default=None), b.span)

    def _try_map_binding_element(self) -> Tagged[MapBindingElement] | None:
        # Named slurp: ...name
        if (ellipsis := self._try_tok(TokenType.Ellipsis)) is not None:
            name = self._try_identifier()
            if name is None:
                self._error(self._here(), ReasonSyntax(SyntaxExpected(SyntaxElement.Identifier)))
                return tag(MapBindingSlurpTo(name="_"), ellipsis.span)
            return tag(MapBindingSlurpTo(name=name.contents), Span.covering(ellipsis.span, name.span))

        # name (as binding)? (= default)?
        name = self._try_identifier()
        if name is None:
            return None

        sub_binding: Tagged[Binding] | None = None
        if self._try_keyword("as") is not None:
            sub_binding = self._require_binding()

        default: Paren[Expr] | None = None
        if self._try_tok(TokenType.Eq) is not None:
            default = self._require_expr()

        if sub_binding is None:
            sub_binding = tag(IdentifierBinding(name=name), name.span)

        end = default.outer() if default is not None else sub_binding.span
        default_inner = default.inner() if default is not None else None
        return tag(
            MapBindingSingleton(key=name, binding=sub_binding, default=default_inner),
            Span.covering(name.span, end),
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
                close_tok_type=TokenType.CloseBracket,
                start_span=open_b.span,
            )
            return tag(ListPatternBinding(binding=lb), Span.covering(open_b.span, close.span))

        # Map pattern: { ... }
        if (open_b := self._try_tok(TokenType.OpenBrace)) is not None:
            mb, close = self._parse_map_binding_terminated(
                lambda: self._try_tok(TokenType.CloseBrace),
                close_tok_type=TokenType.CloseBrace,
                start_span=open_b.span,
            )
            return tag(MapPatternBinding(binding=mb), Span.covering(open_b.span, close.span))

        return None

    def _require_binding(self) -> Tagged[Binding]:
        b = self._try_binding()
        if b is not None:
            return b
        sp = self._here()
        self._error(sp, ReasonSyntax(SyntaxExpected(SyntaxElement.Binding)))
        return self._missing_binding()

    # ── Top-level statements ───────────────────────────────────────────────────

    def _try_import(self) -> ImportStatement | None:
        """import "path" as binding"""
        if self._try_keyword("import") is None:
            return None
        open_q = self._require_tok(TokenType.DoubleQuote)
        path_str = self._try_raw_string_content()
        close_q = self._require_tok(TokenType.DoubleQuote, mode="string")
        path: Tagged[str] = tag(path_str or "", Span.covering(open_q.span, close_q.span))
        self._require_keyword("as")
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

        pexpr = self._try_expr()
        if pexpr is None:
            self._error(self._here(), ReasonSyntax(SyntaxExpected(SyntaxElement.Expression)))
            return File(statements=statements, expression=self._missing_expr())

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
