.PHONY: serve clean vscode

VSCODE_EXT := contrib/vscode-gold

serve: .venv
	rm -rf .cache
	.venv/bin/zensical serve

clean:
	rm -rf .venv .cache site

.venv:
	uv venv .venv
	uv pip install --python .venv/bin/python zensical -e ./docs/lexer

# Launch VS Code with the extension and language server built from source
vscode: $(VSCODE_EXT)/node_modules
	cargo build -p gold --features lsp --bin gold-lsp
	cd $(VSCODE_EXT) && npm run compile
	mkdir -p $(VSCODE_EXT)/bin
	ln -sf ../../../target/debug/gold-lsp $(VSCODE_EXT)/bin/gold-lsp
	code --new-window --extensionDevelopmentPath=$(abspath $(VSCODE_EXT))

$(VSCODE_EXT)/node_modules: $(VSCODE_EXT)/package-lock.json
	cd $(VSCODE_EXT) && npm ci
	touch $@
