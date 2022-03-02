#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Indentifier resolution: Literals", "[bindings]") {
    auto ast = parse_string("1");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {});

    ast = parse_string("true");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {});

    ast = parse_string("\"lolol\"");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {});
}


TEST_CASE("Indentifier resolution: Identifiers", "[bindings]") {
    auto ast = parse_string("dingbob");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"dingbob"});
}


TEST_CASE("Indentifier resolution: Lists", "[bindings]") {
    auto ast = parse_string("[a, b, 1, c, 2.1e3]");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "b", "c"});
}


TEST_CASE("Indentifier resolution: Maps", "[bindings]") {
    auto ast = parse_string("{a: 1, b: a, c: dingbob}");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "dingbob"});
}


TEST_CASE("Indentifier resolution: operator expressions", "[bindings]") {
    auto ast = parse_string("a + 1");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a"});

    ast = parse_string("a + b * 3");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "b"});
}


TEST_CASE("Identifier resolution: blocks", "[bindings]") {
    auto ast = parse_string("let a = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let a = b\nlet c = a\nin c");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let a = b\nin c");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b", "c"});

    ast = parse_string("let [a] = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let [a, ...] = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let [a, ...x] = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let [a, ...x] = b in x");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let {a} = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let {a: b} = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "b"});

    ast = parse_string("let {a: a} = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let {a, ...x} = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse_string("let {a = q, ...x} = b in a");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b", "q"});
}


TEST_CASE("Identifier resolution: functions", "[bindings]") {
    auto ast = parse_string("() => c");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"c"});

    ast = parse_string("(a, b) => a + b + c");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"c"});

    ast = parse_string("(a) => let b = a in b + c");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"c"});
}


TEST_CASE("Identifier resolution: branches", "[bindings]") {
    auto ast = parse_string("if a then b else a + b");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "b"});
}


TEST_CASE("Identifier resolution: function calls", "[bindings]") {
    auto ast = parse_string("some(a, 1, some)");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"some", "a"});
}


TEST_CASE("Identifier resolution: subscripting", "[bindings]") {
    auto ast = parse_string("mylist[1]");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"mylist"});

    ast = parse_string("mylist[index]");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"mylist", "index"});
}
