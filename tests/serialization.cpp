#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Serialization of nulls", "[serialization]") {
    auto val = Object::deserialize(Object::null().serialize());
    REQUIRE(val.type() == Object::Type::null);
    REQUIRE(val.is_null());
}


TEST_CASE("Serialization of integers", "[serialization]") {
    auto val = Object::deserialize(Object::integer(1).serialize());
    REQUIRE(val.type() == Object::Type::integer);
    REQUIRE(val.unsafe_integer() == 1);

    val = Object::deserialize(Object::integer(9223372036854775807).serialize());
    REQUIRE(val.type() == Object::Type::integer);
    REQUIRE(val.unsafe_integer() == 9223372036854775807);

    val = Object::deserialize(Object::integer(-9223372036854775807).serialize());
    REQUIRE(val.type() == Object::Type::integer);
    REQUIRE(val.unsafe_integer() == -9223372036854775807);
}


TEST_CASE("Serialization of strings", "[serialization]") {
    auto val = Object::deserialize(Object::string("").serialize());
    REQUIRE(val.type() == Object::Type::string);
    REQUIRE(val.unsafe_string() == "");

    val = Object::deserialize(Object::string("dingbob").serialize());
    REQUIRE(val.type() == Object::Type::string);
    REQUIRE(val.unsafe_string() == "dingbob");

    val = Object::deserialize(Object::string("ding\"bob").serialize());
    REQUIRE(val.type() == Object::Type::string);
    REQUIRE(val.unsafe_string() == "ding\"bob");
}


TEST_CASE("Serialization of booleans", "[serialization]") {
    auto val = Object::deserialize(Object::boolean(true).serialize());
    REQUIRE(val.type() == Object::Type::boolean);
    REQUIRE(val.unsafe_boolean() == true);

    val = Object::deserialize(Object::boolean(false).serialize());
    REQUIRE(val.type() == Object::Type::boolean);
    REQUIRE(val.unsafe_boolean() == false);
}


TEST_CASE("Serialization of floats", "[serialization]") {
    auto val = Object::deserialize(Object::floating(1.2234).serialize());
    REQUIRE(val.type() == Object::Type::floating);
    REQUIRE(val.unsafe_floating() == 1.2234);
}


TEST_CASE("Serialization of maps", "[serialization]") {
    auto val = Object::deserialize(Object::map({
        {"a", Object::integer(1)},
        {"b", Object::boolean(true)},
        {"c", Object::string("zomg")},
    }).serialize());
    REQUIRE(val.type() == Object::Type::map);
    REQUIRE(val.unsafe_map()->size() == 3);
    REQUIRE((*val.unsafe_map())["a"].unsafe_integer() == 1);
    REQUIRE((*val.unsafe_map())["b"].unsafe_boolean() == true);
    REQUIRE((*val.unsafe_map())["c"].unsafe_string() == "zomg");
}


TEST_CASE("Serialization of lists", "[serialization]") {
    auto val = Object::deserialize(Object::list({
        Object::integer(1),
        Object::string("dingbob"),
        Object::floating(-2.11),
        Object::boolean(false),
    }).serialize());
    REQUIRE(val.type() == Object::Type::list);
    REQUIRE(val.unsafe_list()->size() == 4);
    REQUIRE((*val.unsafe_list())[0].unsafe_integer() == 1);
}


TEST_CASE("Serialization of AST literals", "[serialization]") {
    auto ast = parse_string("1");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("true");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("false");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("-1.23");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("\"dingbob\"");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of AST identifiers", "[serialization]") {
    auto ast = parse_string("dingbob");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("ift");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of list ASTs", "[serialization]") {
    auto ast = parse_string("[]");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("[true]");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("[\"\"]");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("[1, false, -2.3, \"fable\", lel]");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of map ASTs", "[serialization]") {
    auto ast = parse_string("{}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{a: 1}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{che9: false}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{fable: \"fable\"}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: lel}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of opseq ASTs", "[serialization]") {
    auto ast = parse_string("1 + 2");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("1 / 2 + 3");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("1 + 2 - 3 * 4 // 5 / 6");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("1 * (2 + 3)");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of block ASTs", "[serialization]") {
    auto ast = parse_string("{1}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{let a = 1 let b = 2 a + b}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of function ASTs", "[serialization]") {
    auto ast = parse_string("() => 1");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("(a) => {let b = a b}");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of conditional ASTs", "[serialization]") {
    auto ast = parse_string("if true then 1 else 2");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of postfix operator ASTs", "[serialization]") {
    auto ast = parse_string("func(1,2,3)");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("((x,y) => x+y)(1,2)");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("abc.def");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("f(a).x");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("f.x(a)");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("dingbob[\"roflmao\"]");
    REQUIRE(AstNode::deserialize(ast->serialize())->dump() == ast->dump());
}
