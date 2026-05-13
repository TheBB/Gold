from __future__ import annotations

import dataclasses
import json
from enum import Enum
from typing import Any

from .span import Span, Tagged


def pprint(
    node: Any,
    *,
    show_spans: bool = True,
    max_str_len: int | None = None,
) -> str:
    """Return an indented human-readable representation of a parse node or result."""
    pp = _PP(show_spans=show_spans, max_str_len=max_str_len)
    pp._node(node, 0)
    return "\n".join(pp._out)


class _PP:
    _out: list[str]

    def __init__(self, *, show_spans: bool, max_str_len: int | None) -> None:
        self._show_spans = show_spans
        self._max_str_len = max_str_len
        self._out = []

    # ── Helpers ───────────────────────────────────────────────────────────────

    def _emit(self, indent: int, text: str) -> None:
        self._out.append("  " * indent + text)

    def _span(self, span: Span) -> str:
        if not self._show_spans:
            return ""
        return f" [{span.offset}..{span.offset + span.length}]"

    def _strval(self, s: str) -> str:
        if self._max_str_len is not None and len(s) > self._max_str_len:
            return json.dumps(s[: self._max_str_len]) + "..."
        return json.dumps(s)

    def _fmt(self, value: Any) -> str:
        """Format a scalar value (no span)."""
        if isinstance(value, bool):
            return "true" if value else "false"
        if value is None:
            return "null"
        if isinstance(value, Enum):
            return value.name
        if isinstance(value, str):
            return self._strval(value)
        return repr(value)

    def _is_scalar(self, value: Any) -> bool:
        return isinstance(value, (bool, int, float, str, type(None), Enum))

    def _is_dc(self, value: Any) -> bool:
        return dataclasses.is_dataclass(value) and not isinstance(value, type)

    # ── Main dispatch ─────────────────────────────────────────────────────────

    def _node(self, node: Any, indent: int) -> None:
        """Render an arbitrary node at the given indent level."""
        # Import here to avoid circular dependency at module load time
        from .error import Error
        from .parser import ParseResult

        if isinstance(node, Tagged):
            self._tagged(node, indent)
        elif isinstance(node, Error):
            self._emit(indent, "Error")
            self._emit(indent + 1, f"reason: {self._strval(node.message)}")
            if not node.locations:
                self._emit(indent + 1, "locations: []")
            else:
                self._emit(indent + 1, "locations:")
                for span, action in node.locations:
                    self._emit(indent + 2, f"{self._span(span).strip()} {action.name}")
        elif isinstance(node, ParseResult):
            self._emit(indent, "ParseResult")
            self._emit(indent + 1, f"ok: {'true' if node.ok else 'false'}")
            if not node.errors:
                self._emit(indent + 1, "errors: []")
            else:
                self._emit(indent + 1, "errors:")
                for e in node.errors:
                    self._node(e, indent + 2)
            if node.tree is None:
                self._emit(indent + 1, "tree: null")
            else:
                self._emit(indent + 1, "tree:")
                self._node(node.tree, indent + 2)
        elif self._is_dc(node):
            self._emit(indent, type(node).__name__)
            self._fields(node, indent + 1)
        elif isinstance(node, list):
            if not node:
                self._emit(indent, "[]")
            else:
                for item in node:
                    self._node(item, indent)
        elif isinstance(node, tuple):
            for item in node:
                self._node(item, indent)
        elif self._is_scalar(node):
            self._emit(indent, self._fmt(node))
        else:
            self._emit(indent, repr(node))

    def _tagged(self, node: Tagged[Any], indent: int) -> None:
        """Render a Tagged wrapper: emit TypeName [span] then recurse into contents."""
        contents = node.contents
        span_str = self._span(node.span)

        if isinstance(contents, list):
            if not contents:
                self._emit(indent, f"[]{span_str}")
            else:
                self._emit(indent, span_str.lstrip() or "[]")
                for item in contents:
                    self._node(item, indent + 1)
        elif self._is_scalar(contents):
            self._emit(indent, f"{self._fmt(contents)}{span_str}")
        elif self._is_dc(contents):
            self._emit(indent, f"{type(contents).__name__}{span_str}")
            self._fields(contents, indent + 1)
        else:
            self._emit(indent, f"{contents!r}{span_str}")

    def _fields(self, node: Any, indent: int) -> None:
        for field in dataclasses.fields(node):  # type: ignore[arg-type]
            self._field(field.name, getattr(node, field.name), indent)

    def _field(self, name: str, value: Any, indent: int) -> None:
        """Render a named field: `name: value` (scalar) or `name: TypeName` + block."""
        if isinstance(value, Tagged):
            self._field_tagged(name, value, indent)
        elif isinstance(value, list):
            self._field_list(name, value, indent)
        elif value is None:
            self._emit(indent, f"{name}: null")
        elif self._is_scalar(value):
            self._emit(indent, f"{name}: {self._fmt(value)}")
        elif self._is_dc(value):
            self._emit(indent, f"{name}: {type(value).__name__}")
            self._fields(value, indent + 1)
        else:
            self._emit(indent, f"{name}: {value!r}")

    def _field_tagged(self, name: str, value: Tagged[Any], indent: int) -> None:
        contents = value.contents
        span_str = self._span(value.span)

        if isinstance(contents, list):
            if not contents:
                self._emit(indent, f"{name}: []{span_str}")
            else:
                self._emit(indent, f"{name}:{span_str}")
                for item in contents:
                    self._node(item, indent + 1)
        elif self._is_scalar(contents):
            self._emit(indent, f"{name}: {self._fmt(contents)}{span_str}")
        elif self._is_dc(contents):
            self._emit(indent, f"{name}: {type(contents).__name__}{span_str}")
            self._fields(contents, indent + 1)
        else:
            self._emit(indent, f"{name}: {contents!r}{span_str}")

    def _field_list(self, name: str, value: list[Any], indent: int) -> None:
        if not value:
            self._emit(indent, f"{name}: []")
            return
        # Detect list-of-tuples (e.g. LetExpr.bindings) — add [i]: grouping headers.
        if isinstance(value[0], tuple):
            self._emit(indent, f"{name}:")
            for i, item in enumerate(value):
                self._emit(indent + 1, f"[{i}]:")
                assert isinstance(item, tuple)
                for elem in item:
                    self._node(elem, indent + 2)
        else:
            self._emit(indent, f"{name}:")
            for item in value:
                self._node(item, indent + 1)
