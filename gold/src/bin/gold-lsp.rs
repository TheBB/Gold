fn main() {
    tokio::runtime::Runtime::new()
        .expect("failed to create tokio runtime")
        .block_on(gold::lsp::run());
}
