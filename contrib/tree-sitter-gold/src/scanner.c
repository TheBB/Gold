// External scanner for the Gold tree-sitter grammar.
//
// Three external tokens:
//
//   MAP_KEY_IDENT (0)    – identifier-style map key NOT followed by '::'.
//
//   MULTISTRING_KEY (1)  – map key + '::' as a single token.  Including '::'
//                          eliminates the GLR ambiguity that arose when both
//                          map_entry paths shared _map_key_ident as their first
//                          token.  The scanner records the key's start column in
//                          persistent state for use by MULTISTRING_CONTENT.
//
//   MULTISTRING_CONTENT (2) – body of a multiline string.  Uses the column
//                              stored by the most recent MULTISTRING_KEY scan
//                              as the indentation threshold.
//
// Key design: MAP_KEY_IDENT and MULTISTRING_KEY are dispatched in ONE code path.
// The scanner scans the key chars, calls mark_end (end of key), then peeks
// ahead for '::'.  If '::' is found it updates mark_end to include '::' and
// returns MULTISTRING_KEY; otherwise it returns MAP_KEY_IDENT using the earlier
// mark_end.  This avoids advancing + returning false (which would leave the
// lexer in an undefined position relative to the fallback MAP_KEY_IDENT check).

#include "tree_sitter/parser.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum TokenType {
    MAP_KEY_IDENT,
    MULTISTRING_KEY,
    MULTISTRING_CONTENT,
};

typedef struct {
    uint32_t key_col; // start column of last multistring key
} Scanner;

void *tree_sitter_gold_external_scanner_create(void) {
    Scanner *s = malloc(sizeof(Scanner));
    if (s) s->key_col = 0;
    return s;
}

void tree_sitter_gold_external_scanner_destroy(void *p) {
    free(p);
}

unsigned tree_sitter_gold_external_scanner_serialize(void *p, char *buf) {
    Scanner *s = (Scanner *)p;
    memcpy(buf, &s->key_col, sizeof(uint32_t));
    return sizeof(uint32_t);
}

void tree_sitter_gold_external_scanner_deserialize(void *p, const char *buf,
                                                    unsigned len) {
    Scanner *s = (Scanner *)p;
    if (len >= sizeof(uint32_t)) {
        memcpy(&s->key_col, buf, sizeof(uint32_t));
    } else {
        s->key_col = 0;
    }
}

static bool is_key_char(int32_t c) {
    if (c <= 0 || c == '\n' || c == '\r' || c == '\t' || c == ' ')
        return false;
    switch (c) {
        case '\'': case '"':
        case '{':  case '}':
        case '(':  case ')':
        case '[':  case ']':
        case ':':  case ',':
            return false;
        default:
            return true;
    }
}

bool tree_sitter_gold_external_scanner_scan(void *payload, TSLexer *lexer,
                                             const bool *valid_symbols) {
    Scanner *s = (Scanner *)payload;

    // ── MULTISTRING_CONTENT ──────────────────────────────────────────────────
    if (valid_symbols[MULTISTRING_CONTENT]) {
        uint32_t threshold = s->key_col;

        while (!lexer->eof(lexer) && lexer->lookahead != '\n')
            lexer->advance(lexer, false);
        if (!lexer->eof(lexer)) lexer->advance(lexer, false);

        for (;;) {
            if (lexer->eof(lexer)) break;

            uint32_t indent = 0;
            while (lexer->lookahead == ' ' || lexer->lookahead == '\t') {
                indent += (lexer->lookahead == '\t') ? (8 - indent % 8) : 1u;
                lexer->advance(lexer, false);
            }

            if (lexer->lookahead == '\n' || lexer->eof(lexer)) {
                if (!lexer->eof(lexer)) lexer->advance(lexer, false);
                continue;
            }

            if (indent <= threshold) break;

            while (!lexer->eof(lexer) && lexer->lookahead != '\n')
                lexer->advance(lexer, false);
            if (!lexer->eof(lexer)) lexer->advance(lexer, false);
        }

        lexer->mark_end(lexer);
        lexer->result_symbol = MULTISTRING_CONTENT;
        return true;
    }

    // ── MAP_KEY_IDENT / MULTISTRING_KEY ─────────────────────────────────────
    // Handled in one code path to avoid advancing-then-returning-false issues.
    if (valid_symbols[MAP_KEY_IDENT] || valid_symbols[MULTISTRING_KEY]) {
        // Skip whitespace (tree-sitter marks these as extras, but the external
        // scanner must handle them explicitly).
        while (lexer->lookahead == ' ' || lexer->lookahead == '\t' ||
               lexer->lookahead == '\n' || lexer->lookahead == '\r') {
            lexer->advance(lexer, true);
        }

        if (lexer->eof(lexer)) return false;

        int32_t c = lexer->lookahead;
        if (!is_key_char(c) || c == '$' || c == '.') return false;

        uint32_t col = lexer->get_column(lexer);

        while (!lexer->eof(lexer) && is_key_char(lexer->lookahead))
            lexer->advance(lexer, false);

        // Record the end-of-key position.  If we fall back to MAP_KEY_IDENT,
        // this mark_end stays in effect.
        lexer->mark_end(lexer);

        // Peek ahead for '::'.  We continue advancing (WITHOUT updating
        // mark_end) to check whether this is a multistring key.
        if (valid_symbols[MULTISTRING_KEY] && lexer->lookahead == ':') {
            lexer->advance(lexer, false);
            if (lexer->lookahead == ':') {
                lexer->advance(lexer, false);
                // Confirmed '::' — update mark_end to include it.
                s->key_col = col;
                lexer->mark_end(lexer);
                lexer->result_symbol = MULTISTRING_KEY;
                return true;
            }
            // Only one ':' — NOT a multistring key.  mark_end is still at
            // end-of-key, which is what MAP_KEY_IDENT needs.
        }

        if (valid_symbols[MAP_KEY_IDENT]) {
            lexer->result_symbol = MAP_KEY_IDENT;
            return true;
        }

        return false;
    }

    return false;
}
