import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

// Lazily loaded tree-sitter parser.
let Parser: typeof import('web-tree-sitter') | undefined;
let goldParser: import('web-tree-sitter') | undefined;

// ── Activation / deactivation ─────────────────────────────────────────────────

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    // Register language features that don't depend on tree-sitter.
    registerCommands(context);
    context.subscriptions.push(
        vscode.languages.registerDocumentSymbolProvider(
            { language: 'gold' },
            new GoldDocumentSymbolProvider(),
        ),
    );

    // Try to initialise the tree-sitter parser; failures are non-fatal.
    const config = vscode.workspace.getConfiguration('gold');
    if (config.get<boolean>('treeSitter.enabled', true)) {
        try {
            goldParser = await loadParser(context, config.get<string>('treeSitter.wasmPath', ''));
        } catch (err) {
            // Surface a one-time warning but don't block activation.
            vscode.window.showWarningMessage(
                `Gold: failed to load tree-sitter parser — syntax tree features unavailable. ${err}`
            );
        }
    }
}

export function deactivate(): void {
    goldParser = undefined;
    Parser = undefined;
}

// ── Tree-sitter initialisation ────────────────────────────────────────────────

async function loadParser(
    context: vscode.ExtensionContext,
    customWasmPath: string,
): Promise<import('web-tree-sitter')> {
    // web-tree-sitter needs the tree-sitter.wasm runtime.
    if (!Parser) {
        Parser = await import('web-tree-sitter');
        const runtimeWasm = vscode.Uri.joinPath(
            context.extensionUri, 'node_modules', 'web-tree-sitter', 'tree-sitter.wasm'
        );
        await Parser.init({ locateFile: () => runtimeWasm.fsPath });
    }

    const wasmPath = customWasmPath || path.join(context.extensionPath, 'gold.wasm');
    if (!fs.existsSync(wasmPath)) {
        throw new Error(`gold.wasm not found at ${wasmPath}. Build it with 'npm run build-wasm' in contrib/tree-sitter-gold/.`);
    }

    // Capture in a local const so TypeScript narrows away `undefined` across awaits.
    const P = Parser;
    const Gold = await P.Language.load(wasmPath);
    const parser = new P();
    parser.setLanguage(Gold);
    return parser;
}

// ── Commands ──────────────────────────────────────────────────────────────────

function registerCommands(context: vscode.ExtensionContext): void {
    context.subscriptions.push(
        vscode.commands.registerTextEditorCommand('gold.showSyntaxTree', async (editor) => {
            if (editor.document.languageId !== 'gold') return;
            await showSyntaxTree(editor.document);
        }),
    );
}

async function showSyntaxTree(document: vscode.TextDocument): Promise<void> {
    if (!goldParser) {
        vscode.window.showErrorMessage('Gold: tree-sitter parser not loaded.');
        return;
    }

    const tree = goldParser.parse(document.getText());
    const text = renderNode(tree.rootNode, 0);

    const uri = vscode.Uri.parse('gold-syntax-tree:tree');
    const provider = new (class implements vscode.TextDocumentContentProvider {
        provideTextDocumentContent(): string { return text; }
    })();
    const disposable = vscode.workspace.registerTextDocumentContentProvider('gold-syntax-tree', provider);

    const doc = await vscode.workspace.openTextDocument(uri);
    await vscode.window.showTextDocument(doc, { viewColumn: vscode.ViewColumn.Beside, preview: true });

    // Clean up when the tab is closed.
    const closeDisposable = vscode.workspace.onDidCloseTextDocument(closed => {
        if (closed.uri.toString() === uri.toString()) {
            disposable.dispose();
            closeDisposable.dispose();
        }
    });
    return;
}

// ── Tree pretty-printer ───────────────────────────────────────────────────────

function renderNode(node: import('web-tree-sitter').SyntaxNode, depth: number): string {
    const indent = '  '.repeat(depth);
    const named = node.isNamed;
    if (!named && node.childCount === 0) return '';

    const label = named ? node.type : `"${node.type}"`;
    const loc = `[${node.startPosition.row}:${node.startPosition.column}–${node.endPosition.row}:${node.endPosition.column}]`;
    let result = `${indent}${label} ${loc}`;
    if (node.childCount === 0 && node.text.length <= 40) {
        result += ` "${node.text.replace(/\n/g, '\\n')}"`;
    }
    result += '\n';

    for (const child of node.children) {
        result += renderNode(child, depth + 1);
    }
    return result;
}

// ── Document symbol provider (uses tree-sitter when available) ────────────────

class GoldDocumentSymbolProvider implements vscode.DocumentSymbolProvider {
    provideDocumentSymbols(
        document: vscode.TextDocument,
    ): vscode.DocumentSymbol[] {
        if (!goldParser) return [];
        const tree = goldParser.parse(document.getText());
        return extractSymbols(tree.rootNode, document);
    }
}

function extractSymbols(
    node: import('web-tree-sitter').SyntaxNode,
    document: vscode.TextDocument,
): vscode.DocumentSymbol[] {
    const symbols: vscode.DocumentSymbol[] = [];

    if (node.type === 'map_entry') {
        const keyNode = node.childForFieldName('key');
        if (keyNode) {
            const range = nodeRange(keyNode);
            const full = nodeRange(node);
            const sym = new vscode.DocumentSymbol(
                keyNode.text,
                '',
                vscode.SymbolKind.Property,
                full,
                range,
            );
            sym.children = extractSymbols(node, document).filter(
                s => full.contains(s.range)
            );
            symbols.push(sym);
        }
    }

    for (const child of node.children) {
        symbols.push(...extractSymbols(child, document));
    }

    return symbols;
}

function nodeRange(node: import('web-tree-sitter').SyntaxNode): vscode.Range {
    return new vscode.Range(
        node.startPosition.row,
        node.startPosition.column,
        node.endPosition.row,
        node.endPosition.column,
    );
}
