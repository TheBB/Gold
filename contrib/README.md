# Gold editor tooling

This directory contains editor integrations for the Gold language.

## Directory layout

| Path | Description |
|------|-------------|
| `tree-sitter-gold/` | Tree-sitter grammar (C parser + external scanner) |
| `vscode-gold/` | VS Code extension |

---

## tree-sitter-gold

A tree-sitter grammar for Gold.  The grammar handles the full language including
multi-line strings (`key:: ...`), which are indentation-sensitive and require the
external C scanner in `src/scanner.c`.

### Building

```sh
cd contrib/tree-sitter-gold
npm install
make generate   # runs tree-sitter generate → produces src/parser.c
make wasm       # runs tree-sitter build --wasm → produces gold.wasm
make test       # run the corpus tests (requires tests/corpus/*.txt)
```

Requirements: [tree-sitter CLI](https://github.com/tree-sitter/tree-sitter/blob/master/cli/README.md)

```sh
npm install -g tree-sitter-cli
# or with cargo:
cargo install tree-sitter-cli
```

### How multi-line strings work

Gold supports a long-form string value in maps:

```gold
{
    description:: This is the first line
                  and this is a continuation
    other-key: "normal value"
}
```

The string continues on every subsequent line whose **indentation is strictly
greater than the column of the key** (`description` is at column 4, so only
lines indented by 5+ spaces are included).

Pure tree-sitter grammars cannot express this because the termination condition
is dynamic (depends on the column of a previously seen token).  The external
scanner (`src/scanner.c`) handles it with **three external tokens**:

1. `_map_key_ident` — regular map key (not followed by `::`).
2. `_multistring_key` — map key **plus** the `::` consumed together as one
   token.  The scanner records the key's start column in persistent state.
   Combining key + `::` into a single token is crucial: it eliminates the GLR
   ambiguity that would otherwise arise because both `map_entry` alternatives
   (regular and multistring) used to start with the same external token.
3. `_multistring_content` — consumed after `_multistring_key`; reads the stored
   column as the indentation threshold and consumes lines until one is found
   whose first non-whitespace character is at or before that threshold.

The scanner handles `_map_key_ident` and `_multistring_key` in a single code
path: it scans the key chars, calls `mark_end` (just past the key), then peeks
ahead for `::`.  If found, it updates `mark_end` to include `::` and emits
`_multistring_key`; otherwise it emits `_map_key_ident` using the earlier
`mark_end`.  This design avoids advancing past characters and then returning
false (which would leave the lexer at the wrong position for the fallback).

---

## vscode-gold

A VS Code extension that provides:

- **Syntax highlighting** via a TextMate grammar (`syntaxes/gold.tmLanguage.json`)
  — works immediately with no compilation step.
- **Tree-sitter integration** via `web-tree-sitter` — enables the *Gold: Show
  Syntax Tree* command and richer language features.  Requires `gold.wasm` to be
  built and placed in the extension directory.

### Quick start (TextMate highlighting only)

```sh
cd contrib/vscode-gold
npm install
npm run compile
# In VS Code: F5 to open the Extension Development Host
```

### Full setup (with tree-sitter)

```sh
# 1. Build the WASM parser
cd contrib/tree-sitter-gold
npm install && make wasm   # produces gold.wasm in this directory AND copies it to ../vscode-gold/

# 2. Build and launch the extension
cd ../vscode-gold
npm install
npm run compile
# In VS Code: F5
```

### Commands

| Command | Description |
|---------|-------------|
| `Gold: Show Syntax Tree` | Open a side panel showing the tree-sitter parse tree for the current file |

### Settings

| Setting | Default | Description |
|---------|---------|-------------|
| `gold.treeSitter.enabled` | `true` | Enable tree-sitter features |
| `gold.treeSitter.wasmPath` | `""` | Override path to `gold.wasm` |
