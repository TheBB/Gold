from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto


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


# ── ObjectType ────────────────────────────────────────────────────────────────


class ObjectType(Enum):
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
            case ObjectType.Integer:
                return "int"
            case ObjectType.Float:
                return "float"
            case ObjectType.String:
                return "str"
            case ObjectType.Boolean:
                return "bool"
            case ObjectType.List:
                return "list"
            case ObjectType.Map:
                return "map"
            case ObjectType.Function:
                return "function"
            case ObjectType.Iterator:
                return "iterator"
            case ObjectType.Null:
                return "null"
