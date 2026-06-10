import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

type SyntaxNode = import('web-tree-sitter').SyntaxNode;

// Lazily loaded tree-sitter parser.
let Parser: typeof import('web-tree-sitter') | undefined;
let goldParser: import('web-tree-sitter') | undefined;

// ── Semantic token legend ─────────────────────────────────────────────────────

const TOKEN_TYPES = [
    'comment', 'string', 'number', 'keyword', 'operator',
    'variable', 'parameter', 'property', 'function',
] as const;

const TOKEN_MODIFIERS = ['declaration'] as const;

const LEGEND = new vscode.SemanticTokensLegend(
    [...TOKEN_TYPES],
    [...TOKEN_MODIFIERS],
);

// Gold control-flow and logical keywords (appear as anonymous tree nodes).
const KEYWORDS = new Set([
    'let', 'in', 'if', 'then', 'else', 'fn', 'for', 'when', 'import', 'as',
    'and', 'or', 'not', 'has',
]);

// Symbolic operators (appear as anonymous tree nodes).
const OPERATORS = new Set([
    '+', '-', '*', '/', '//', '^',
    '==', '!=', '<', '<=', '>', '>=',
    '=', '...',
]);

// ── Activation / deactivation ─────────────────────────────────────────────────

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    registerCommands(context);
    context.subscriptions.push(
        vscode.languages.registerDocumentSymbolProvider(
            { language: 'gold' },
            new GoldDocumentSymbolProvider(),
        ),
        vscode.languages.registerDocumentSemanticTokensProvider(
            { language: 'gold' },
            new GoldSemanticTokensProvider(),
            LEGEND,
        ),
    );

    // Try to initialise the tree-sitter parser; failures are non-fatal.
    const config = vscode.workspace.getConfiguration('gold');
    if (config.get<boolean>('treeSitter.enabled', true)) {
        try {
            goldParser = await loadParser(context, config.get<string>('treeSitter.wasmPath', ''));
        } catch (err) {
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

    const closeDisposable = vscode.workspace.onDidCloseTextDocument(closed => {
        if (closed.uri.toString() === uri.toString()) {
            disposable.dispose();
            closeDisposable.dispose();
        }
    });
    return;
}

// ── Tree pretty-printer ───────────────────────────────────────────────────────

function renderNode(node: SyntaxNode, depth: number): string {
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

// ── Semantic tokens provider ──────────────────────────────────────────────────

class GoldSemanticTokensProvider implements vscode.DocumentSemanticTokensProvider {
    provideDocumentSemanticTokens(
        document: vscode.TextDocument,
    ): vscode.SemanticTokens | undefined {
        if (!goldParser) return undefined;
        const tree = goldParser.parse(document.getText());
        const builder = new vscode.SemanticTokensBuilder(LEGEND);
        visitNode(tree.rootNode, builder, document);
        return builder.build();
    }
}

// Walk the tree in document order, emitting semantic tokens for each node.
// Named leaf nodes and anonymous keyword/operator nodes are emitted directly.
// All other named nodes recurse into their children.
function visitNode(
    node: SyntaxNode,
    builder: vscode.SemanticTokensBuilder,
    doc: vscode.TextDocument,
): void {
    switch (node.type) {
        case 'comment':
            pushToken(node, 'comment', [], builder, doc);
            return;

        case 'literal':
            // 'true', 'false', 'null' are language constants; everything else is numeric.
            pushToken(node, /^[0-9]|^\./.test(node.text) ? 'number' : 'keyword', [], builder, doc);
            return;

        case 'string_raw':
        case 'multistring':
        case 'format_spec':
            pushToken(node, 'string', [], builder, doc);
            return;

        case 'map_key_ident':
            pushToken(node, 'property', [], builder, doc);
            return;

        case 'identifier': {
            const parent = node.parent;
            if (parent?.type === 'call_expr' && parent.childForFieldName('function') === node) {
                pushToken(node, 'function', [], builder, doc);
            } else if (parent?.type === 'identifier_binding') {
                pushToken(node, 'variable', ['declaration'], builder, doc);
            } else if (parent?.type === 'map_binding_entry' && parent.childForFieldName('key') === node) {
                // Keyword parameter name in fn ({key; key2=default}) or map destructuring.
                pushToken(node, 'parameter', ['declaration'], builder, doc);
            } else {
                pushToken(node, 'variable', [], builder, doc);
            }
            return;
        }
    }

    if (!node.isNamed) {
        const text = node.text;
        if (KEYWORDS.has(text)) {
            pushToken(node, 'keyword', [], builder, doc);
        } else if (OPERATORS.has(text)) {
            pushToken(node, 'operator', [], builder, doc);
        }
        return;
    }

    for (const child of node.children) {
        visitNode(child, builder, doc);
    }
}

// Push a semantic token for the given node.  The semantic tokens API requires
// each token to lie on a single line, so multi-line nodes (multistring content)
// are split into per-line segments.
function pushToken(
    node: SyntaxNode,
    type: string,
    modifiers: string[],
    builder: vscode.SemanticTokensBuilder,
    doc: vscode.TextDocument,
): void {
    const startRow = node.startPosition.row;
    const endRow = node.endPosition.row;

    if (startRow === endRow) {
        builder.push(
            new vscode.Range(startRow, node.startPosition.column, startRow, node.endPosition.column),
            type,
            modifiers,
        );
        return;
    }

    // Multi-line: emit one segment per line.
    for (let row = startRow; row <= endRow; row++) {
        const lineLen = doc.lineAt(row).text.length;
        const startCol = row === startRow ? node.startPosition.column : 0;
        const endCol   = row === endRow   ? node.endPosition.column   : lineLen;
        if (endCol > startCol) {
            builder.push(
                new vscode.Range(row, startCol, row, endCol),
                type,
                modifiers,
            );
        }
    }
}

// ── Document symbol provider ──────────────────────────────────────────────────

class GoldDocumentSymbolProvider implements vscode.DocumentSymbolProvider {
    provideDocumentSymbols(
        document: vscode.TextDocument,
    ): vscode.DocumentSymbol[] {
        if (!goldParser) return [];
        const tree = goldParser.parse(document.getText());
        return extractSymbols(tree.rootNode, document);
    }
}

function extractSymbols(node: SyntaxNode, document: vscode.TextDocument): vscode.DocumentSymbol[] {
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
            sym.children = extractSymbols(node, document).filter(s => full.contains(s.range));
            symbols.push(sym);
        }
    }

    for (const child of node.children) {
        symbols.push(...extractSymbols(child, document));
    }

    return symbols;
}

function nodeRange(node: SyntaxNode): vscode.Range {
    return new vscode.Range(
        node.startPosition.row,
        node.startPosition.column,
        node.endPosition.row,
        node.endPosition.column,
    );
}
