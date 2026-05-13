# Gold — Programmable Configuration Language

Gold is a programmable configuration language that serves as an alternative to JSON, YAML, TOML, and similar formats. It occupies the same niche as Dhall but with a more familiar syntax, a less constraining type system, and first-class support for functions (functions are valid output values).

## Repository layout

| Path | Description |
|------|-------------|
| `gold/` | Main Rust implementation — library crate with associated binaries |
| `goldpy/` | Python bindings (PyO3-based Rust extension) |
| `ref/` | Reference Python implementation (in development) |
| `docs/` | Zensical documentation |
| `examples/` | Example `.gold` files |

## Language overview

A Gold file consists of zero or more top-level `import` statements followed by a **single expression** whose value is the result of the file.

**Types:** integers, floats, strings (double-quoted), `null`, `true`, `false`, lists, objects (string-keyed maps), and functions.

**Key features:**
- Let-bindings: `let x = 1 let y = 2 in x + y`
- Destructuring in let-bindings, function parameters, and for-loops (list and object patterns, with defaults and slurp/rest)
- Branching: `if condition then expr else expr` (else is mandatory; everything is truthy except `false`, `null`, `0`, `0.0`)
- Functions: `fn (x, y) x + y` — always anonymous, form closures, support positional and keyword parameters separated by `;`
- Advanced collections: conditional elements (`if cond: elem`), for-loops (`for x in list: expr`), splat (`...expr`)
- String interpolation: `"${expr}"` with Python-style format specs (`"${n:.2f}"`)
- Long-form strings: `key:: text until dedent` inside objects
- Imports: `import "path.gold" as name` — relative paths, statements only, evaluated eagerly

## Rust implementation (`gold/`)

**Entry points:**
- `gold/src/lib.rs` — public API
- `gold/src/lexing.rs` — lexer (nom-based)
- `gold/src/parsing.rs` — parser (nom-based)
- `gold/src/ast/` — high-level (`high.rs`) and low-level (`low.rs`) AST, scope analysis
- `gold/src/compile.rs` — compilation to low-level IR
- `gold/src/eval.rs` — evaluator
- `gold/src/formatting.rs` — string format-spec handling
- `gold/src/object/` — runtime value types
- `gold/src/builtins.rs` — built-in functions
- `gold/src/bin/` — CLI binaries (`gold-to-json`, `gold-parsecheck`)

**Required checks:**
```sh
cargo check
cargo test
```

## Python reference implementation (`ref/`)

A clean Python reimplementation of the full Gold pipeline. Currently implements the lexer, parser, and AST; evaluation is in progress.

**Source layout:**
- `ref/src/ref/lexer.py` — tokenizer
- `ref/src/ref/parser.py` — recursive-descent parser
- `ref/src/ref/ast.py` — AST node dataclasses
- `ref/src/ref/span.py` — source-span / `Tagged[T]` wrapper

**Required check (must always pass):**
```sh
cd ref && make test
```

`make test` runs: `pytest`, `pyrefly` (type checker), `ruff check`, and `ruff format --check`.

**Python conventions (mandatory):**
- `from __future__ import annotations` at the top of every file
- New-style type aliases: `type X = ...`
- New-style generic syntax: `def func[T](...) -> ...`
- All functions fully typed — parameters and return type, including test functions
- All classes should have attributes typed at the top level, before the constructor
- Use `pyrefly` (not mypy/pyright) for type checking

**Tooling:**
- Package manager: `uv`; run tools via `uv run <tool>`
- Linter/formatter: `ruff` (line length 110)
- Type checker: `pyrefly`
- Test runner: `pytest`

## Python bindings (`goldpy/`)

PyO3-based Rust extension that exposes the `gold` crate to Python. Built as part of the Cargo workspace via the `python` feature flag.

## Documentation (`docs/`)

Zensical site. Source files:
- `docs/index.md` — introduction and motivation
- `docs/whirlwind.md` — full language tour
- `docs/formatting.md` — string format-spec reference
- `docs/lexer/` — Pygments lexer for syntax highlighting
