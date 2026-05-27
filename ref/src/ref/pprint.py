from __future__ import annotations

import dataclasses
import json
from enum import Enum
from typing import TYPE_CHECKING, Any, TypedDict, Unpack

from .ast import GoldBuiltin, GoldFunction, GoldValue
from .span import Span, Tagged


if TYPE_CHECKING:
    from .error import Error
    from .evaluation import EvalResult
    from .parser import ParseResult


def _render_tree(raw: list[tuple[int, str]]) -> list[str]:
    n = len(raw)

    def _is_last(i: int) -> bool:
        depth = raw[i][0]
        for j in range(i + 1, n):
            d = raw[j][0]
            if d < depth:
                return True
            if d == depth:
                return False
        return True

    def _ancestor_at(i: int, depth: int) -> int | None:
        for k in range(i - 1, -1, -1):
            d = raw[k][0]
            if d == depth:
                return k
            if d < depth:
                return None
        return None

    out: list[str] = []
    for i, (depth, text) in enumerate(raw):
        if depth == 0:
            out.append(text)
            continue

        last = _is_last(i)

        parts: list[str] = []
        for lvl in range(1, depth):
            anc = _ancestor_at(i, lvl)
            if anc is not None and not _is_last(anc):
                parts.append("│   ")
            else:
                parts.append("    ")

        connector = "╰── " if last else "├── "
        out.append("".join(parts) + connector + text)

    return out


class PrintOpts(TypedDict, total=False):
    show_spans: bool
    max_str_len: int | None
    tree: bool


def pprint_parse_result(
    node: ParseResult,
    **kwargs: Unpack[PrintOpts],
) -> str:
    """Return a human-readable representation of a ParseResult."""
    pp = _PP(**kwargs)
    pp._parse_result(node, 0)
    return "\n".join(pp._render())


def pprint_eval_result(
    node: EvalResult,
    **kwargs: Unpack[PrintOpts],
) -> str:
    """Return a human-readable representation of an EvalResult."""
    pp = _PP(**kwargs)
    pp._eval_result(node, 0)
    return "\n".join(pp._render())


class _PP:
    _raw: list[tuple[int, str]]

    def __init__(self, **kwargs: Unpack[PrintOpts]) -> None:
        self._show_spans = kwargs.get("show_spans", False)
        self._max_str_len = kwargs.get("max_str_len")
        self._tree = kwargs.get("tree", False)
        self._raw = []

    def _render(self) -> list[str]:
        if self._tree:
            return _render_tree(self._raw)
        return ["  " * depth + text for depth, text in self._raw]

    # ── Helpers ───────────────────────────────────────────────────────────────

    def _emit(self, indent: int, text: str) -> None:
        self._raw.append((indent, text))

    def _span(self, span: Span) -> str:
        if not self._show_spans:
            return ""
        return f" [{span.offset}..{span.offset + span.length}]"

    def _strval(self, s: str) -> str:
        if self._max_str_len is not None and len(s) > self._max_str_len:
            return json.dumps(s[: self._max_str_len]) + "..."
        return json.dumps(s, ensure_ascii=False)

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

    # ── Gold value rendering ──────────────────────────────────────────────────

    def _gold_label(self, value: GoldValue) -> str:
        """The inline label for a gold value (used on the same line as a field name)."""
        if value is None:
            return "null"
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, int):
            return str(value)
        if isinstance(value, float):
            return repr(value)
        if isinstance(value, str):
            return self._strval(value)
        if isinstance(value, GoldBuiltin):
            return f"(builtin {value.name})"
        if isinstance(value, GoldFunction):
            return "(function)"
        if isinstance(value, list):
            return "(list) []" if not value else "(list)"
        if isinstance(value, dict):
            return "(map) {}" if not value else "(map)"
        return repr(value)

    def _gold_value(self, value: GoldValue, indent: int) -> None:
        """Emit the label for a value then its body (if non-scalar)."""
        self._emit(indent, self._gold_label(value))
        if isinstance(value, list) and value:
            for i, item in enumerate(value):
                self._emit(indent + 1, f"[{i}]:")
                self._gold_value(item, indent + 2)
        elif isinstance(value, dict) and value:
            for k, v in value.items():
                self._gold_field(k, v, indent + 1)

    def _gold_field(self, name: str, value: GoldValue, indent: int) -> None:
        """Emit  `name: <label>`  and, for non-empty collections, the body below."""
        self._emit(indent, f"{name}: {self._gold_label(value)}")
        if isinstance(value, list) and value:
            for i, item in enumerate(value):
                self._emit(indent + 1, f"[{i}]:")
                self._gold_value(item, indent + 2)
        elif isinstance(value, dict) and value:
            for k, v in value.items():
                self._gold_field(k, v, indent + 1)

    # ── Result-type rendering ─────────────────────────────────────────────────

    def _error(self, node: Error, indent: int) -> None:
        self._emit(indent, "Error")
        self._emit(indent + 1, f"reason: {self._strval(node.message)}")
        if not node.locations:
            self._emit(indent + 1, "locations: []")
        else:
            self._emit(indent + 1, "locations:")
            for span, action in node.locations:
                self._emit(indent + 2, f"{self._span(span).strip()} {action.name}")

    def _eval_result(self, node: EvalResult, indent: int) -> None:
        self._emit(indent, "EvalResult")
        self._emit(indent + 1, f"ok: {'true' if node.ok else 'false'}")
        if node.error is not None:
            self._emit(indent + 1, "error:")
            self._error(node.error, indent + 2)
        else:
            self._gold_field("value", node.value, indent + 1)

    def _parse_result(self, node: ParseResult, indent: int) -> None:
        self._emit(indent, "ParseResult")
        self._emit(indent + 1, f"ok: {'true' if node.ok else 'false'}")
        if not node.errors:
            self._emit(indent + 1, "errors: []")
        else:
            self._emit(indent + 1, "errors:")
            for e in node.errors:
                self._error(e, indent + 2)
        if node.tree is None:
            self._emit(indent + 1, "tree: null")
        else:
            self._emit(indent + 1, "tree:")
            self._node(node.tree, indent + 2)

    # ── Main dispatch ─────────────────────────────────────────────────────────

    def _node(self, node: Any, indent: int) -> None:
        """Render an arbitrary node at the given indent level."""
        if isinstance(node, Tagged):
            self._tagged(node, indent)
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
                for i, item in enumerate(contents):
                    self._emit(indent + 1, f"[{i}]:")
                    self._node(item, indent + 2)
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
                for i, item in enumerate(contents):
                    self._emit(indent + 1, f"[{i}]:")
                    self._node(item, indent + 2)
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
        self._emit(indent, f"{name}:")
        for i, item in enumerate(value):
            self._emit(indent + 1, f"[{i}]:")
            if isinstance(item, tuple):
                for elem in item:
                    self._node(elem, indent + 2)
            else:
                self._node(item, indent + 2)
