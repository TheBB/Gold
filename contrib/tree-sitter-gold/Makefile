.PHONY: all generate wasm test clean

all: generate

# Generate the C parser from grammar.js.
# Requires: npm install -g tree-sitter-cli  (or npx tree-sitter)
generate: grammar.js src/scanner.c
	node_modules/.bin/tree-sitter generate

# Build the WebAssembly parser for use in the VSCode extension.
# After this succeeds, copy gold.wasm to ../vscode-gold/
wasm: generate
	node_modules/.bin/tree-sitter build --wasm
	cp tree-sitter-gold.wasm ../vscode-gold/gold.wasm

# Run the tree-sitter test suite (tests/corpus/).
test: generate
	tree-sitter test

clean:
	rm -rf src/parser.c src/tree_sitter/ bindings/node/ tree-sitter-gold.wasm node_modules/
