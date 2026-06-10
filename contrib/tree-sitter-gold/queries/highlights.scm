; Gold syntax highlight queries for tree-sitter.
;
; These node names correspond to the grammar defined in grammar.js.
; Highlight names follow the standard tree-sitter convention used by Neovim,
; Helix, and the VSCode tree-sitter integration.

; ── Keywords ──────────────────────────────────────────────────────────────────

[
  "let" "in"
  "if" "then" "else"
  "fn"
  "for" "in" "when"
  "import" "as"
] @keyword

[
  "and" "or" "not"
] @keyword.operator

"has" @keyword.operator

; ── Literals ──────────────────────────────────────────────────────────────────

(literal) @constant.builtin

[ "true" "false" ] @boolean
"null" @constant.builtin

; Integers and floats get a more specific highlight.
((literal) @number
 (#match? @number "[0-9]"))

; ── Strings ───────────────────────────────────────────────────────────────────

(string) @string
(string_raw) @string
(multistring) @string

(string_interpolation) @string.special
(string_interpolation "$" @punctuation.special)
(string_interpolation "{" @punctuation.special)
(string_interpolation "}" @punctuation.special)
(format_spec) @string.special.key

; ── Identifiers ───────────────────────────────────────────────────────────────

(identifier) @variable
(identifier_binding (identifier) @variable)

; Function names — when an identifier is immediately called
(call_expr
  function: (identifier) @function.call)

(dot_expr
  key: (identifier) @variable.member)

; Map keys
(map_key_ident) @variable.member
(map_entry
  key: (string) @variable.member)

; Import path
(import_statement
  path: (string) @string.special.path)

; Binding names in let / fn / for
(identifier_binding
  (identifier) @variable)

(map_binding_entry
  key: (identifier) @variable.parameter)

(list_binding_entry
  binding: (identifier_binding
    (identifier) @variable.parameter))

; ── Operators ─────────────────────────────────────────────────────────────────

[
  "+"  "-"  "*"  "/"  "//"  "^"
  "==" "!=" "<"  "<=" ">"  ">="
  "="
] @operator

[ "..." ] @operator

; ── Punctuation ───────────────────────────────────────────────────────────────

[ "(" ")" "[" "]" "{" "}" "{|" "|}" ] @punctuation.bracket
[ "," ":" ";" "." ] @punctuation.delimiter
"$" @punctuation.special

; ── Comments ──────────────────────────────────────────────────────────────────

(comment) @comment @spell
