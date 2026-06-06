import XCTest
import SwiftTreeSitter
import TreeSitterGold

final class TreeSitterGoldTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_gold())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Gold grammar")
    }
}
