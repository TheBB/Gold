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
    REQUIRE(val.size() == 4);
    REQUIRE(val[0].unsafe_integer() == 1);
}


TEST_CASE("Serialization of functions", "[serialization]") {
    auto val = Object::deserialize(evaluate_string("(x, y) => x + y").serialize());
    REQUIRE(val.type() == Object::Type::function);
    REQUIRE(val(Object::integer(1), Object::integer(2)).unsafe_integer() == 3);

    val = Object::deserialize(evaluate_string("let a = 1 in () => a").serialize());
    REQUIRE(val.type() == Object::Type::function);
    REQUIRE(val().unsafe_integer() == 1);

    val = Object::deserialize(evaluate_string("(x) => [1, if x: 1, for t in [x]: t, ...[x]]").serialize());
    REQUIRE(val(Object::boolean(true)).size() == 4);
    REQUIRE(val(Object::boolean(false)).size() == 3);

    val = Object::deserialize(evaluate_string(
        "(x) => {a: 1, if x: b: 1, for [k,v] in items({c: 1}): $k: v, ...{d: 1}}"
    ).serialize());
    REQUIRE(val(Object::boolean(true)).size() == 4);
    REQUIRE(val(Object::boolean(false)).size() == 3);
}


TEST_CASE("Serialization of builtins", "[serialization]") {
    auto val = Object::deserialize(evaluate_string("int").serialize());
    REQUIRE(val.type() == Object::Type::function);
    REQUIRE(val(Object::string("12")).unsafe_integer() == 12);
}


TEST_CASE("Serialization of duplicate object", "[serialization]") {
    auto val = Object::deserialize(evaluate_string("let a = [] in [a, a]").serialize());
    REQUIRE(val.type() == Object::Type::list);
    REQUIRE(val.size() == 2);
    REQUIRE(val[0].type() == Object::Type::list);
    REQUIRE(val[0].size() == 0);
    REQUIRE(val[1].type() == Object::Type::list);
    REQUIRE(val[1].size() == 0);
    REQUIRE(val[0].unsafe_list().get() == val[1].unsafe_list().get());
}


TEST_CASE("Serialization of AST literals", "[serialization]") {
    auto ast = parse_string("1");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("true");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("false");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("-1.23");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("\"dingbob\"");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of AST identifiers", "[serialization]") {
    auto ast = parse_string("dingbob");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("ift");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of list ASTs", "[serialization]") {
    auto ast = parse_string("[]");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("[true]");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("[\"\"]");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("[1, false, -2.3, \"fable\", lel]");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of map ASTs", "[serialization]") {
    auto ast = parse_string("{}");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{a: 1}");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{che9: false}");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{fable: \"fable\"}");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: lel}");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of opseq ASTs", "[serialization]") {
    auto ast = parse_string("1 + 2");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("1 / 2 + 3");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("1 + 2 - 3 * 4 // 5 / 6");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("1 * (2 + 3)");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of block ASTs", "[serialization]") {
    auto ast = parse_string("let a = 1\nlet b = 2\nin a + b");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let [a] = [1] in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let [a, b] = [1, 2] in [a, b]");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let [a = 1] = [] in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let [a, ...] = [1] in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let [a, ...x] = [1] in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a: b} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a = 1} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a: b = 1} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {b, a = 1} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a: b, ...x} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a, ...x} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a = 1, ...x} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("let {a: b = 1, ...x} = c in a");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of function ASTs", "[serialization]") {
    auto ast = parse_string("() => 1");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("(a) => let b = a in b");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of conditional ASTs", "[serialization]") {
    auto ast = parse_string("if true then 1 else 2");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}


TEST_CASE("Serialization of postfix operator ASTs", "[serialization]") {
    auto ast = parse_string("func(1,2,3)");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("((x,y) => x+y)(1,2)");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("abc.def");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("f(a).x");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("f.x(a)");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());

    ast = parse_string("dingbob[\"roflmao\"]");
    REQUIRE(Expr::deserialize(ast->serialize())->dump() == ast->dump());
}
