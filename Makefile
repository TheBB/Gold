.PHONY: serve clean

serve: .venv
	rm -rf .cache
	.venv/bin/zensical serve

clean:
	rm -rf .venv .cache site

.venv:
	uv venv .venv
	uv pip install --python .venv/bin/python zensical -e ./docs/lexer
