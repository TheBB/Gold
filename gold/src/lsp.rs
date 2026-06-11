#![allow(missing_docs)]

use std::collections::HashMap;

use tokio::sync::Mutex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::error::Span;

pub struct Backend {
    client: Client,
    documents: Mutex<HashMap<Url, String>>,
}

impl Backend {
    async fn parse_and_publish(&self, uri: Url, source: &str) {
        let diagnostics = {
            let result = crate::parse(source);
            result.errors.iter().map(error_to_diagnostic).collect::<Vec<_>>()
        }; // result dropped here, before the await
        self.client.publish_diagnostics(uri, diagnostics, None).await;
    }
}

fn span_to_range(span: Span) -> Range {
    let start = Position::new(span.line(), span.column());
    // Spans are byte-based; for a PoC treating them as character offsets is
    // fine for ASCII source. Full UTF-16 accounting can come later.
    let end = Position::new(span.line(), span.column() + span.length() as u32);
    Range { start, end }
}

fn error_to_diagnostic(err: &crate::Error) -> Diagnostic {
    let range = err.location().map(span_to_range).unwrap_or_default();
    Diagnostic {
        range,
        severity: Some(DiagnosticSeverity::ERROR),
        message: err.reason_display(),
        ..Default::default()
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _params: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "gold-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _params: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "gold-lsp initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        self.parse_and_publish(uri.clone(), &text).await;
        self.documents.lock().await.insert(uri, text);
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // With FULL sync there is always exactly one entry, but be defensive.
        if let Some(change) = params.content_changes.into_iter().last() {
            let uri = params.text_document.uri;
            self.parse_and_publish(uri.clone(), &change.text).await;
            self.documents.lock().await.insert(uri, change.text);
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        self.documents.lock().await.remove(&uri);
        self.client.publish_diagnostics(uri, vec![], None).await;
    }
}

pub async fn run() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    let (service, socket) = LspService::new(|client| Backend {
        client,
        documents: Mutex::new(HashMap::new()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}
