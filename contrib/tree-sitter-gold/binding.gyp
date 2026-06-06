{
  "targets": [
    {
      "target_name": "tree_sitter_gold_binding",
      "include_dirs": [
        "<!@(node -p \"require('node-addon-api').include_dir\")",
        "node_modules/tree-sitter/src"
      ],
      "sources": [
        "bindings/node/binding.cc",
        "src/parser.c",
        "src/scanner.c"
      ],
      "cflags_c": ["-std=c11"],
      "defines": ["NAPI_VERSION=8", "NODE_ADDON_API_DISABLE_CPP_EXCEPTIONS"]
    }
  ]
}
