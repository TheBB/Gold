from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Callable


@dataclass(frozen=True)
class Position:
    """A location in a source buffer (all fields are zero-indexed)."""

    offset: int
    line: int
    column: int

    @classmethod
    def zero(cls) -> Position:
        return cls(0, 0, 0)

    def adjust(self, offset: int, delta_line: int = 0) -> Position:
        """Move a position forward by `offset` bytes and `delta_line` lines.

        Use delta_line=0 to move within a line.  Moving to the start of a new
        line and then into it requires two calls (this avoids ambiguity about
        the column).
        """
        return Position(
            offset=self.offset + offset,
            line=self.line + delta_line,
            column=0 if delta_line > 0 else self.column + offset,
        )

    def with_length(self, length: int) -> Span:
        return Span(start=self, length=length)

    def __sub__(self, rhs: Position) -> Span:
        return rhs.with_length(self.offset - rhs.offset)


@dataclass(frozen=True)
class Span:
    """An interval of text in a source buffer: a start position and a length."""

    start: Position
    length: int

    @property
    def offset(self) -> int:
        return self.start.offset

    @property
    def line(self) -> int:
        return self.start.line

    @property
    def column(self) -> int:
        return self.start.column

    def with_length(self, length: int) -> Span:
        return Span(start=self.start, length=length)

    def with_line(self, line: int) -> Span:
        return Span(
            start=Position(self.start.offset, line, self.start.column),
            length=self.length,
        )

    def with_column(self, column: int) -> Span:
        return Span(
            start=Position(self.start.offset, self.start.line, column),
            length=self.length,
        )

    def with_coord(self, line: int, column: int) -> Span:
        return self.with_line(line).with_column(column)

    @classmethod
    def from_offsets(cls, start: int, end: int) -> Span:
        """Span covering [start, end) on line 0."""
        return cls(start=Position(start, 0, start), length=end - start)

    @classmethod
    def from_offset(cls, offset: int) -> Span:
        """Single-character span at offset on line 0."""
        return cls(start=Position(offset, 0, offset), length=1)

    @classmethod
    def covering(cls, start: Span, end: Span) -> Span:
        """Span from the start of `start` to the end of `end`."""
        return cls(start=start.start, length=end.offset + end.length - start.offset)


@dataclass(frozen=True)
class Tagged[T]:
    """Wraps any value with the source span it originated from."""

    span: Span
    contents: T

    def unwrap(self) -> T:
        return self.contents

    def decompose(self) -> tuple[T, Span]:
        return (self.contents, self.span)

    def map[U](self, f: Callable[[T], U]) -> Tagged[U]:
        return Tagged(span=self.span, contents=f(self.contents))

    def wrap[U](self, f: Callable[[Tagged[T]], U]) -> Tagged[U]:
        return Tagged(span=self.span, contents=f(self))

    def retag(self, span: Span) -> Tagged[T]:
        return Tagged(span=span, contents=self.contents)

    def with_coord(self, line: int, column: int) -> Tagged[T]:
        return self.retag(self.span.with_coord(line, column))

    def __repr__(self) -> str:
        s = self.span
        return f"{self.contents!r}.tag({s.line + 1}:{s.column + 1}, {s.offset}..{s.offset + s.length})"


def tag[T](value: T, span: Span) -> Tagged[T]:
    """Wrap `value` with `span` (Python equivalent of the Taggable trait)."""
    return Tagged(span=span, contents=value)


@dataclass(frozen=True)
class Paren[T]:
    """An expression that may be wrapped in parentheses.

    Mirrors the Rust ``Paren<T>`` enum:

    - ``Naked(Tagged<T>)``                  inner span == outer span
    - ``Parenthesized(Tagged<Tagged<T>>)``  inner span is the expression itself;
                                            outer span includes surrounding parens

    Use ``inner()`` when storing an expression in an AST node.
    Use ``outer()`` when computing the span of the enclosing construct.
    """

    _inner: Tagged[T]
    _outer: Span | None = None  # None → Naked (outer == _inner.span)

    @classmethod
    def naked(cls, expr: Tagged[T]) -> Paren[T]:
        return cls(_inner=expr)

    @classmethod
    def parenthesized(cls, inner: Tagged[T], outer: Span) -> Paren[T]:
        return cls(_inner=inner, _outer=outer)

    def inner(self) -> Tagged[T]:
        """The expression with its own span (parentheses excluded)."""
        return self._inner

    def outer(self) -> Span:
        """The outermost span, including any surrounding parentheses."""
        return self._outer if self._outer is not None else self._inner.span

    def map_wrap[U](self, f: Callable[[Tagged[T]], U]) -> Paren[U]:
        """Wrap the inner content with *f* while preserving paren structure."""
        return Paren(_inner=self._inner.wrap(f), _outer=self._outer)
