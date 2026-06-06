// swift-tools-version:5.3
import PackageDescription

let package = Package(
    name: "TreeSitterGold",
    products: [
        .library(name: "TreeSitterGold", targets: ["TreeSitterGold"]),
    ],
    dependencies: [
        .package(url: "https://github.com/ChimeHQ/SwiftTreeSitter", from: "0.8.0"),
    ],
    targets: [
        .target(
            name: "TreeSitterGold",
            dependencies: [],
            path: ".",
            sources: [
                "src/parser.c",
                // NOTE: if your language has an external scanner, add it here.
            ],
            resources: [
                .copy("queries")
            ],
            publicHeadersPath: "bindings/swift",
            cSettings: [.headerSearchPath("src")]
        ),
        .testTarget(
            name: "TreeSitterGoldTests",
            dependencies: [
                "SwiftTreeSitter",
                "TreeSitterGold",
            ],
            path: "bindings/swift/TreeSitterGoldTests"
        )
    ],
    cLanguageStandard: .c11
)
