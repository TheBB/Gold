package tree_sitter_gold_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_gold "github.com/tree-sitter/tree-sitter-gold/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_gold.Language())
	if language == nil {
		t.Errorf("Error loading Gold grammar")
	}
}
