.PHONY: serve clean vscode vscode-vsix vscode-build

VSCODE_EXT := contrib/vscode-gold
VSCODE_TEST := $(abspath $(VSCODE_EXT))/.vscode-test

serve: .venv
	rm -rf .cache
	.venv/bin/zensical serve

clean:
	rm -rf .venv .cache site

.venv:
	uv venv .venv
	uv pip install --python .venv/bin/python zensical -e ./docs/lexer

# Launch VS Code with the extension and language server built from source
vscode: vscode-build
	code --new-window --extensionDevelopmentPath=$(abspath $(VSCODE_EXT))

# Package the extension as a VSIX and launch it in a fresh, isolated VS Code profile
vscode-vsix: vscode-build
	rm -rf $(VSCODE_TEST)
	mkdir -p $(VSCODE_TEST)
	cd $(VSCODE_EXT) && npx @vscode/vsce package -o $(VSCODE_TEST)/goldlang.vsix
	code --extensions-dir $(VSCODE_TEST)/extensions --user-data-dir $(VSCODE_TEST)/user \
		--install-extension $(VSCODE_TEST)/goldlang.vsix
	code --extensions-dir $(VSCODE_TEST)/extensions --user-data-dir $(VSCODE_TEST)/user --new-window

vscode-build: $(VSCODE_EXT)/node_modules
	cargo build -p gold --features lsp --bin gold-lsp
	cd $(VSCODE_EXT) && npm run bundle
	mkdir -p $(VSCODE_EXT)/bin
	ln -sf ../../../target/debug/gold-lsp $(VSCODE_EXT)/bin/gold-lsp

$(VSCODE_EXT)/node_modules: $(VSCODE_EXT)/package-lock.json
	cd $(VSCODE_EXT) && npm ci
	touch $@
