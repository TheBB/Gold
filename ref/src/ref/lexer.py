from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import TYPE_CHECKING

from .span import Position, Tagged, tag

if TYPE_CHECKING:
    from collections.abc import Callable

# ── Token types ───────────────────────────────────────────────────────────────


class TokenType(Enum):
    Asterisk = auto()
    Caret = auto()
    CloseBrace = auto()
    CloseBracePipe = auto()
    CloseBracket = auto()
    CloseParen = auto()
    Colon = auto()
    Comma = auto()
    Dollar = auto()
    Dot = auto()
    DoubleColon = auto()
    DoubleEq = auto()
    DoubleSlash = auto()
    DoubleQuote = auto()
    Ellipsis = auto()
    Eq = auto()
    ExclamEq = auto()
    Greater = auto()
    GreaterEq = auto()
    Less = auto()
    LessEq = auto()
    Minus = auto()
    OpenBrace = auto()
    OpenBracePipe = auto()
    OpenBracket = auto()
    OpenParen = auto()
    Pipe = auto()
    Plus = auto()
    SemiColon = auto()
    Slash = auto()
    Name = auto()
    Float = auto()
    Integer = auto()
    StringLit = auto()
    MultiString = auto()
    Char = auto()

    def __str__(self) -> str:
        match self:
            case TokenType.Asterisk:
                return "'*'"
            case TokenType.Caret:
                return "'^'"
            case TokenType.CloseBrace:
                return "'}'"
            case TokenType.CloseBracePipe:
                return "'|}'"
            case TokenType.CloseBracket:
                return "']'"
            case TokenType.CloseParen:
                return "')'"
            case TokenType.Colon:
                return "':'"
            case TokenType.Comma:
                return "','"
            case TokenType.Dollar:
                return "'$'"
            case TokenType.Dot:
                return "'.'"
            case TokenType.DoubleColon:
                return "'::'"
            case TokenType.DoubleEq:
                return "'=='"
            case TokenType.DoubleSlash:
                return "'//'"
            case TokenType.DoubleQuote:
                return "'\"'"
            case TokenType.Ellipsis:
                return "'...'"
            case TokenType.Eq:
                return "'='"
            case TokenType.ExclamEq:
                return "'!='"
            case TokenType.Greater:
                return "'>'"
            case TokenType.GreaterEq:
                return "'>='"
            case TokenType.Less:
                return "'<'"
            case TokenType.LessEq:
                return "'<='"
            case TokenType.Minus:
                return "'-'"
            case TokenType.OpenBrace:
                return "'{'"
            case TokenType.OpenBracePipe:
                return "'{|'"
            case TokenType.OpenBracket:
                return "'['"
            case TokenType.OpenParen:
                return "'('"
            case TokenType.Pipe:
                return "'|'"
            case TokenType.Plus:
                return "'+'"
            case TokenType.SemiColon:
                return "';'"
            case TokenType.Slash:
                return "'/'"
            case TokenType.Name:
                return "name"
            case TokenType.Float:
                return "float"
            case TokenType.Integer:
                return "int"
            case TokenType.StringLit:
                return "string literal"
            case TokenType.MultiString:
                return "multi-line string literal"
            case TokenType.Char:
                return "character"


# ── Token ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class Token:
    kind: TokenType
    text: str


@dataclass(frozen=True)
class MissingToken:
    """Sentinel for a token that was expected but not present in the source."""

    kind: TokenType


# ── Errors ────────────────────────────────────────────────────────────────────


class LexError(Exception):
    position: Position
    reason: str

    def __init__(self, position: Position, reason: str) -> None:
        super().__init__(f"{reason} at {position.line + 1}:{position.column + 1}")
        self.position = position
        self.reason = reason


# ── Regexes ───────────────────────────────────────────────────────────────────

_WHITESPACE = re.compile(r"[^\S\n]*")
_NAME = re.compile(r"""[a-zA-Z_][^\s'"{}()\[\]/+*\-;:,.=#|^]*""")
_KEY = re.compile(r"""[^\s'"{}()\[\]:]+""")
_FLOAT_A = re.compile(r"[0-9][0-9_]*\.[0-9_]*(?:(?:e|E)(?:\+|-)?[0-9][0-9_]*)?")
_FLOAT_B = re.compile(r"\.[0-9][0-9_]*(?:(?:e|E)[0-9][0-9_]*)?")
_FLOAT_C = re.compile(r"[0-9][0-9_]*(?:e|E)(?:\+|-)?[0-9][0-9_]*")
_DIGITS = re.compile(r"[0-9][0-9_]*")
_PUREDIGITS = re.compile(r"[1-9][0-9]*")


# ── Lexer ─────────────────────────────────────────────────────────────────────

type LexResult = tuple[Lexer, Tagged[Token]]


@dataclass(frozen=True)
class Lexer:
    code: str
    position: Position = field(default_factory=Position.zero)

    @classmethod
    def new(cls, code: str) -> Lexer:
        return cls(code=code, position=Position.zero())

    def _peek(self) -> str | None:
        return self.code[0] if self.code else None

    def _char_at(self, i: int) -> str | None:
        return self.code[i] if i < len(self.code) else None

    def _satisfies_at(self, i: int, f: Callable[[str], bool]) -> bool:
        c = self._char_at(i)
        return c is not None and f(c)

    def _skip(self, offset: int, delta_line: int) -> Lexer:
        return Lexer(
            code=self.code[offset:],
            position=self.position.adjust(offset, delta_line),
        )

    def _skip_tag(self, offset: int, delta_line: int, kind: TokenType) -> LexResult:
        span = self.position.with_length(offset)
        return self._skip(offset, delta_line), tag(Token(kind, self.code[:offset]), span)

    def _traverse(self, pattern: re.Pattern[str], kind: TokenType) -> LexResult:
        m = pattern.match(self.code)
        if m is None:
            c = self._peek()
            reason = "unexpected end of input" if c is None else f"unexpected '{c}'"
            raise LexError(self.position, reason)
        return self._skip_tag(m.end(), 0, kind)

    def _skip_indent(self) -> Lexer:
        m = _WHITESPACE.match(self.code)
        assert m is not None
        return self._skip(m.end(), 0)

    def _skip_whitespace(self) -> Lexer:
        cur = self
        while True:
            cur = cur._skip_indent()
            c = cur._peek()
            if c == "\n":
                cur = cur._skip(1, 1)
            elif c == "#":
                nl = cur.code.find("\n")
                end = nl if nl >= 0 else len(cur.code) - 1
                cur = cur._skip(end + 1, 1)
            else:
                break
        return cur

    def _next_number(self) -> LexResult:
        for pattern, kind in (
            (_FLOAT_A, TokenType.Float),
            (_FLOAT_B, TokenType.Float),
            (_FLOAT_C, TokenType.Float),
            (_DIGITS, TokenType.Integer),
        ):
            m = pattern.match(self.code)
            if m is not None:
                return self._skip_tag(m.end(), 0, kind)
        raise LexError(self.position, "expected number")

    def _next_name(self, pattern: re.Pattern[str]) -> LexResult:
        return self._traverse(pattern, TokenType.Name)

    def _next_pure_integer(self) -> LexResult:
        return self._traverse(_PUREDIGITS, TokenType.Integer)

    def error(self, reason: str) -> LexError:
        return LexError(self.position, reason)

    def _tokenize_default(self) -> LexResult:
        cur = self._skip_whitespace()
        c = cur._peek()

        if c is None:
            raise LexError(cur.position, "unexpected end of input")
        if c.isascii() and (c.isalpha() or c == "_"):
            return cur._next_name(_NAME)
        if c.isdigit() or (c == "." and cur._satisfies_at(1, str.isdigit)):
            return cur._next_number()
        if c == "." and cur._satisfies_at(1, lambda x: x == ".") and cur._satisfies_at(2, lambda x: x == "."):
            return cur._skip_tag(3, 0, TokenType.Ellipsis)
        if c == ".":
            return cur._skip_tag(1, 0, TokenType.Dot)
        if c == ":" and cur._satisfies_at(1, lambda x: x == ":"):
            return cur._skip_tag(2, 0, TokenType.DoubleColon)
        if c == ":":
            return cur._skip_tag(1, 0, TokenType.Colon)
        if c == '"':
            return cur._skip_tag(1, 0, TokenType.DoubleQuote)
        if c == "{" and cur._satisfies_at(1, lambda x: x == "|"):
            return cur._skip_tag(2, 0, TokenType.OpenBracePipe)
        if c == "{":
            return cur._skip_tag(1, 0, TokenType.OpenBrace)
        if c == "|" and cur._satisfies_at(1, lambda x: x == "}"):
            return cur._skip_tag(2, 0, TokenType.CloseBracePipe)
        if c == "}":
            return cur._skip_tag(1, 0, TokenType.CloseBrace)
        if c == "[":
            return cur._skip_tag(1, 0, TokenType.OpenBracket)
        if c == "]":
            return cur._skip_tag(1, 0, TokenType.CloseBracket)
        if c == "(":
            return cur._skip_tag(1, 0, TokenType.OpenParen)
        if c == ")":
            return cur._skip_tag(1, 0, TokenType.CloseParen)
        if c == ",":
            return cur._skip_tag(1, 0, TokenType.Comma)
        if c == "+":
            return cur._skip_tag(1, 0, TokenType.Plus)
        if c == "-":
            return cur._skip_tag(1, 0, TokenType.Minus)
        if c == "/" and cur._satisfies_at(1, lambda x: x == "/"):
            return cur._skip_tag(2, 0, TokenType.DoubleSlash)
        if c == "/":
            return cur._skip_tag(1, 0, TokenType.Slash)
        if c == "*":
            return cur._skip_tag(1, 0, TokenType.Asterisk)
        if c == "^":
            return cur._skip_tag(1, 0, TokenType.Caret)
        if c == "<" and cur._satisfies_at(1, lambda x: x == "="):
            return cur._skip_tag(2, 0, TokenType.LessEq)
        if c == "<":
            return cur._skip_tag(1, 0, TokenType.Less)
        if c == ">" and cur._satisfies_at(1, lambda x: x == "="):
            return cur._skip_tag(2, 0, TokenType.GreaterEq)
        if c == ">":
            return cur._skip_tag(1, 0, TokenType.Greater)
        if c == "=" and cur._satisfies_at(1, lambda x: x == "="):
            return cur._skip_tag(2, 0, TokenType.DoubleEq)
        if c == "=":
            return cur._skip_tag(1, 0, TokenType.Eq)
        if c == "!" and cur._satisfies_at(1, lambda x: x == "="):
            return cur._skip_tag(2, 0, TokenType.ExclamEq)
        if c == "|":
            return cur._skip_tag(1, 0, TokenType.Pipe)
        if c == ";":
            return cur._skip_tag(1, 0, TokenType.SemiColon)
        raise LexError(cur.position, f"unexpected '{c}'")

    def _tokenize_map(self) -> LexResult:
        cur = self._skip_whitespace()
        c = cur._peek()

        if c is None:
            raise LexError(cur.position, "unexpected end of input")
        if c == "}":
            return cur._skip_tag(1, 0, TokenType.CloseBrace)
        if c == "$":
            return cur._skip_tag(1, 0, TokenType.Dollar)
        if c == '"':
            return cur._skip_tag(1, 0, TokenType.DoubleQuote)
        if c == ":" and cur._satisfies_at(1, lambda x: x == ":"):
            return cur._skip_tag(2, 0, TokenType.DoubleColon)
        if c == ":":
            return cur._skip_tag(1, 0, TokenType.Colon)
        if c == "." and cur._satisfies_at(1, lambda x: x == ".") and cur._satisfies_at(2, lambda x: x == "."):
            return cur._skip_tag(3, 0, TokenType.Ellipsis)
        return cur._next_name(_KEY)

    def _tokenize_string(self) -> LexResult:
        c = self._peek()
        if c is None:
            raise LexError(self.position, "unexpected end of input")
        if c == '"':
            return self._skip_tag(1, 0, TokenType.DoubleQuote)
        if c == "$":
            return self._skip_tag(1, 0, TokenType.Dollar)
        if c == "\n":
            raise LexError(self.position, "unexpected newline in string")

        i = 0
        while i < len(self.code):
            c = self.code[i]
            if c in ('"', "$", "\n"):
                return self._skip_tag(i, 0, TokenType.StringLit)
            if c == "\\" and i + 1 < len(self.code):
                nc = self.code[i + 1]
                if nc in ('"', "\\", "$"):
                    i += 2
                    continue
                raise LexError(self._skip(i + 1, 0).position, f"unexpected '{nc}'")
            i += 1

        return self._skip_tag(len(self.code), 0, TokenType.StringLit)

    def _tokenize_multistring(self, col: int) -> LexResult:
        orig = self
        nl = self.code.find("\n")
        end = nl if nl >= 0 else len(self.code) - 1
        cur = self._skip(end + 1, 1)

        while True:
            skipped = cur._skip_indent()
            if skipped.position.column <= col:
                break
            nl = skipped.code.find("\n")
            end = nl if nl >= 0 else len(self.code) - 1  # matches Rust: uses orig self.code len
            cur = skipped._skip(end + 1, 1)

        span = cur.position - orig.position
        return cur, tag(Token(TokenType.MultiString, orig.code[: span.length]), span)

    def _tokenize_fmtspec(self) -> LexResult:
        c = self._peek()
        if c is None:
            raise LexError(self.position, "unexpected end of input")
        if c == "\n":
            raise LexError(self.position, "unexpected newline in format spec")
        if c == "}":
            return self._skip_tag(1, 0, TokenType.CloseBrace)
        if "1" <= c <= "9":
            return self._next_pure_integer()
        return self._skip_tag(1, 0, TokenType.Char)

    # ── Public API (mirrors CachedLexer in Rust) ──────────────────────────────

    def next_token(self) -> LexResult:
        return self._tokenize_default()

    def next_key(self) -> LexResult:
        return self._tokenize_map()

    def next_string(self) -> LexResult:
        return self._tokenize_string()

    def next_multistring(self, col: int) -> LexResult:
        return self._tokenize_multistring(col)

    def next_fmtspec(self) -> LexResult:
        return self._tokenize_fmtspec()

    def skip_whitespace(self) -> Lexer:
        return self._skip_whitespace()
