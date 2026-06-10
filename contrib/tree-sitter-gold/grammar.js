// Tree-sitter grammar for the Gold configuration language.
//
// Multi-line strings (key:: ...) are indentation-sensitive and require the
// external scanner in src/scanner.c. All other constructs are handled here.

module.exports = grammar({
  name: 'gold',

  externals: $ => [
    // Regular identifier-style map key (NOT followed by '::').
    $._map_key_ident,
    // Map key followed immediately by '::'.  The scanner records the key's
    // column so _multistring_content knows the threshold.  Including '::' in
    // this token eliminates the GLR ambiguity between the two map_entry paths
    // (both previously started with _map_key_ident, causing persistent dual
    // parse states).
    $._multistring_key,
    // Content of a multi-line string (consumed after _multistring_key).
    $._multistring_content,
  ],

  extras: $ => [
    /\s/,
    $.comment,
  ],

  // 'identifier' is the word token: tree-sitter uses it to distinguish keywords
  // from plain names.
  word: $ => $.identifier,

  conflicts: $ => [],

  rules: {
    // ── Top level ──────────────────────────────────────────────────────────────

    source_file: $ => seq(
      repeat($.import_statement),
      $._expr,
    ),

    comment: _ => /#[^\n]*/,

    import_statement: $ => seq(
      'import',
      field('path', $.string),
      'as',
      field('binding', $._binding),
    ),

    // ── Expressions ────────────────────────────────────────────────────────────

    _expr: $ => choice(
      $.let_expr,
      $.if_expr,
      $.fn_expr,
      $.fn_old_kw_expr,
      $.fn_old_pos_expr,
      $._disjunction,
    ),

    // let b1 = e1  let b2 = e2  in body
    let_expr: $ => seq(
      'let',
      field('binding', $._binding),
      '=',
      field('value', $._expr),
      repeat(seq(
        'let',
        field('binding', $._binding),
        '=',
        field('value', $._expr),
      )),
      'in',
      field('body', $._expr),
    ),

    // if cond then true_branch else false_branch
    if_expr: $ => seq(
      'if',
      field('condition', $._expr),
      'then',
      field('consequence', $._expr),
      'else',
      field('alternative', $._expr),
    ),

    // fn (pos ; kw) body  |  fn {kw} body
    fn_expr: $ => seq(
      'fn',
      field('params', choice(
        $.fn_paren_params,
        $.fn_brace_params,
      )),
      field('body', $._expr),
    ),

    fn_paren_params: $ => seq(
      '(',
      optional($._list_binding_inner),
      optional(seq(';', optional($._map_binding_inner))),
      ')',
    ),

    fn_brace_params: $ => seq(
      '{',
      optional($._map_binding_inner),
      '}',
    ),

    // {| kw |} body  (deprecated)
    fn_old_kw_expr: $ => seq(
      '{|',
      optional($._map_binding_inner),
      '|}',
      field('body', $._expr),
    ),

    // | pos | body  |  | pos ; kw | body  (deprecated)
    fn_old_pos_expr: $ => seq(
      '|',
      optional($._list_binding_inner),
      optional(seq(';', optional($._map_binding_inner))),
      '|',
      field('body', $._expr),
    ),

    // ── Operator hierarchy (prec values match Python parser levels) ────────────

    _disjunction: $ => choice(
      $.binary_expr_or,
      $._conjunction,
    ),

    binary_expr_or: $ => prec.left(1, seq(
      field('left', $._disjunction),
      field('operator', 'or'),
      field('right', $._conjunction),
    )),

    _conjunction: $ => choice(
      $.binary_expr_and,
      $._contains,
    ),

    binary_expr_and: $ => prec.left(2, seq(
      field('left', $._conjunction),
      field('operator', 'and'),
      field('right', $._contains),
    )),

    _contains: $ => choice(
      $.binary_expr_has,
      $._equality,
    ),

    binary_expr_has: $ => prec.left(3, seq(
      field('left', $._contains),
      field('operator', 'has'),
      field('right', $._equality),
    )),

    _equality: $ => choice(
      $.binary_expr_eq,
      $._comparison,
    ),

    binary_expr_eq: $ => prec.left(4, seq(
      field('left', $._equality),
      field('operator', choice('==', '!=')),
      field('right', $._comparison),
    )),

    _comparison: $ => choice(
      $.binary_expr_cmp,
      $._sum,
    ),

    binary_expr_cmp: $ => prec.left(5, seq(
      field('left', $._comparison),
      field('operator', choice('<', '<=', '>', '>=')),
      field('right', $._sum),
    )),

    _sum: $ => choice(
      $.binary_expr_add,
      $._product,
    ),

    binary_expr_add: $ => prec.left(6, seq(
      field('left', $._sum),
      field('operator', choice('+', '-')),
      field('right', $._product),
    )),

    _product: $ => choice(
      $.binary_expr_mul,
      $._prefix,
    ),

    binary_expr_mul: $ => prec.left(7, seq(
      field('left', $._product),
      field('operator', choice('*', '/', '//')),
      field('right', $._prefix),
    )),

    _prefix: $ => choice(
      $.unary_expr,
      $._power,
    ),

    unary_expr: $ => prec.right(8, seq(
      field('operator', choice('+', '-', 'not')),
      field('operand', $._prefix),
    )),

    _power: $ => choice(
      $.binary_expr_pow,
      $._postfix,
    ),

    // Right-associative: a ^ -b  (the exponent can be a prefix expression)
    binary_expr_pow: $ => prec.right(9, seq(
      field('left', $._postfix),
      field('operator', '^'),
      field('right', $._prefix),
    )),

    _postfix: $ => choice(
      $.call_expr,
      $.index_expr,
      $.dot_expr,
      $._primary,
    ),

    call_expr: $ => prec.left(10, seq(
      field('function', $._postfix),
      '(',
      optional($._arg_list),
      ')',
    )),

    index_expr: $ => prec.left(10, seq(
      field('object', $._postfix),
      '[',
      field('index', $._expr),
      ']',
    )),

    dot_expr: $ => prec.left(10, seq(
      field('object', $._postfix),
      '.',
      field('key', $.identifier),
    )),

    _primary: $ => choice(
      $.parenthesized_expr,
      $.identifier,
      $.literal,
      $.string,
      $.list,
      $.map,
    ),

    parenthesized_expr: $ => seq('(', $._expr, ')'),

    // ── Atoms ──────────────────────────────────────────────────────────────────

    identifier: _ => /[a-zA-Z_][^\s'"{}()\[\]\/+*\-;:,.=#|^]*/,

    literal: _ => choice(
      'null',
      'true',
      'false',
      /[0-9][0-9_]*\.[0-9_]*(?:[eE][+-]?[0-9][0-9_]*)?/,  // float a
      /\.[0-9][0-9_]*(?:[eE][0-9][0-9_]*)?/,               // float b
      /[0-9][0-9_]*[eE][+-]?[0-9][0-9_]*/,                 // float c
      /[0-9][0-9_]*/,                                       // integer
    ),

    // ── Strings ────────────────────────────────────────────────────────────────

    // Adjacent string literals are concatenated: "a" "b" → "ab"
    // prec.left resolves the ambiguity between consuming another '"'-started
    // part vs. ending the string expression.
    string: $ => prec.left(seq(
      $._string_part,
      repeat($._string_part),
    )),

    _string_part: $ => seq(
      '"',
      repeat($._string_content),
      '"',
    ),

    _string_content: $ => choice(
      $.string_raw,
      $.string_interpolation,
    ),

    string_raw: _ => /[^"$\n\\]+|\\["\\$]/,

    string_interpolation: $ => seq(
      '$',
      choice(
        // $name  (simple identifier interpolation)
        field('expr', $.identifier),
        // ${expr}  or  ${expr:fmt}
        seq(
          '{',
          field('expr', $._expr),
          optional(seq(':', field('format_spec', $.format_spec))),
          '}',
        ),
      ),
    ),

    // Format spec: everything up to the closing '}'
    // Kept opaque for highlighting purposes; semantic parsing can extend this.
    format_spec: _ => /[^}]*/,

    // ── Lists ──────────────────────────────────────────────────────────────────

    list: $ => seq(
      '[',
      optional(seq(
        $._list_element,
        repeat(seq(',', $._list_element)),
        optional(','),
      )),
      ']',
    ),

    _list_element: $ => choice(
      $.list_splat,
      $.list_for,
      $.list_when,
      $._expr,
    ),

    list_splat: $ => seq('...', $._expr),

    list_for: $ => seq(
      'for',
      field('binding', $._binding),
      'in',
      field('iterable', $._expr),
      ':',
      field('element', $._list_element),
    ),

    list_when: $ => seq(
      'when',
      field('condition', $._expr),
      ':',
      field('element', $._list_element),
    ),

    // ── Maps ───────────────────────────────────────────────────────────────────

    map: $ => seq(
      '{',
      optional(seq(
        $._map_element,
        repeat(seq(optional(','), $._map_element)),
        optional(','),
      )),
      '}',
    ),

    _map_element: $ => choice(
      $.map_splat,
      $.map_for,
      $.map_when,
      $.map_entry,
    ),

    map_splat: $ => seq('...', $._expr),

    map_for: $ => seq(
      'for',
      field('binding', $._binding),
      'in',
      field('iterable', $._expr),
      ':',
      field('element', $._map_element),
    ),

    map_when: $ => seq(
      'when',
      field('condition', $._expr),
      ':',
      field('element', $._map_element),
    ),

    map_entry: $ => choice(
      // Regular entry: key: value
      seq(
        field('key', $._map_key),
        ':',
        field('value', $._expr),
      ),
      // Multi-line string entry: key:: content
      // _multistring_key is a SINGLE external token that consumes the identifier
      // AND the '::' together.  This eliminates the GLR ambiguity that arose when
      // both paths shared _map_key_ident as their first token.
      seq(
        field('key', alias($._multistring_key, $.map_key_ident)),
        field('value', alias($._multistring_content, $.multistring)),
      ),
      // Dynamic key: $expr: value
      seq(
        '$',
        field('key', $._expr),
        ':',
        field('value', $._expr),
      ),
    ),

    _map_key: $ => choice(
      alias($._map_key_ident, $.map_key_ident),
      $.string,
    ),

    // ── Function arguments ─────────────────────────────────────────────────────

    _arg_list: $ => seq(
      $._arg_element,
      repeat(seq(',', $._arg_element)),
      optional(','),
    ),

    _arg_element: $ => choice(
      $.arg_splat,
      $.arg_keyword,
      $._expr,
    ),

    arg_splat: $ => seq('...', $._expr),

    // keyword: value  (only when ':' immediately follows the identifier)
    arg_keyword: $ => seq(
      field('key', $.identifier),
      ':',
      field('value', $._expr),
    ),

    // ── Bindings ───────────────────────────────────────────────────────────────

    _binding: $ => choice(
      $.identifier_binding,
      $.list_pattern_binding,
      $.map_pattern_binding,
    ),

    identifier_binding: $ => $.identifier,

    list_pattern_binding: $ => seq(
      '[',
      optional(seq(
        $._list_binding_element,
        repeat(seq(',', $._list_binding_element)),
        optional(','),
      )),
      ']',
    ),

    map_pattern_binding: $ => seq(
      '{',
      optional(seq(
        $._map_binding_element,
        repeat(seq(',', $._map_binding_element)),
        optional(','),
      )),
      '}',
    ),

    _list_binding_inner: $ => seq(
      $._list_binding_element,
      repeat(seq(',', $._list_binding_element)),
      optional(','),
    ),

    _map_binding_inner: $ => seq(
      $._map_binding_element,
      repeat(seq(',', $._map_binding_element)),
      optional(','),
    ),

    _list_binding_element: $ => choice(
      $.list_binding_slurp,
      $.list_binding_entry,
    ),

    list_binding_slurp: $ => seq(
      '...',
      optional($.identifier),
    ),

    list_binding_entry: $ => seq(
      field('binding', $._binding),
      optional(seq('=', field('default', $._expr))),
    ),

    _map_binding_element: $ => choice(
      $.map_binding_slurp,
      $.map_binding_entry,
    ),

    map_binding_slurp: $ => seq('...', $.identifier),

    map_binding_entry: $ => seq(
      field('key', $.identifier),
      optional(seq('as', field('binding', $._binding))),
      optional(seq('=', field('default', $._expr))),
    ),
  },
});
