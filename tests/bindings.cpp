#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Indentifier resolution: Literals", "[bindings]") {
    auto ast = parse("1");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {});

    ast = parse("true");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {});

    ast = parse("\"lolol\"");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {});
}


TEST_CASE("Indentifier resolution: Identifiers", "[bindings]") {
    auto ast = parse("dingbob");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"dingbob"});
}


TEST_CASE("Indentifier resolution: Lists", "[bindings]") {
    auto ast = parse("[a, b, 1, c, 2.1e3]");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "b", "c"});
}


TEST_CASE("Indentifier resolution: Maps", "[bindings]") {
    auto ast = parse("{a: 1, b: a, c: dingbob}");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "dingbob"});
}


TEST_CASE("Indentifier resolution: operator expressions", "[bindings]") {
    auto ast = parse("a + 1");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a"});

    ast = parse("a + b * 3");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "b"});
}


TEST_CASE("Identifier resolution: blocks", "[bindings]") {
    auto ast = parse("{let a = b\na}");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse("{let a = b\nlet c = a\nc}");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b"});

    ast = parse("{let a = b\nc}");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"b", "c"});
}


TEST_CASE("Identifier resolution: functions", "[bindings]") {
    auto ast = parse("() => c");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"c"});

    ast = parse("(a, b) => a + b + c");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"c"});

    ast = parse("(a) => {let b = a\nb + c}");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"c"});
}


TEST_CASE("Identifier resolution: branches", "[bindings]") {
    auto ast = parse("if a then b else a + b");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"a", "b"});
}


TEST_CASE("Identifier resolution: function calls", "[bindings]") {
    auto ast = parse("some(a, 1, some)");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"some", "a"});
}


TEST_CASE("Identifier resolution: subscripting", "[bindings]") {
    auto ast = parse("mylist[1]");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"mylist"});

    ast = parse("mylist[index]");
    REQUIRE(ast->free_identifiers() == std::set<std::string> {"mylist", "index"});
}
