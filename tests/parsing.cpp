#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Grammar is well-formed", "[parsing]") {
    REQUIRE(analyze_grammar());
}


TEST_CASE("Parse booleans", "[parsing]") {
    auto obj = parse("true").unsafe_object();
    REQUIRE(obj.type() == Object::Type::boolean);
    REQUIRE(obj.unsafe_boolean() == true);

    obj = parse("false").unsafe_object();
    REQUIRE(obj.type() == Object::Type::boolean);
    REQUIRE(obj.unsafe_boolean() == false);
}


TEST_CASE("Parse integers", "[parsing]") {
    auto obj = parse("0").unsafe_object();
    REQUIRE(obj.type() == Object::Type::integer);
    REQUIRE(obj.unsafe_integer() == 0);

    obj = parse("1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::integer);
    REQUIRE(obj.unsafe_integer() == 1);

    obj = parse("+1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::integer);
    REQUIRE(obj.unsafe_integer() == 1);

    obj = parse("-1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::integer);
    REQUIRE(obj.unsafe_integer() == -1);

    obj = parse("9223372036854775807").unsafe_object();
    REQUIRE(obj.type() == Object::Type::integer);
    REQUIRE(obj.unsafe_integer() == 9223372036854775807);

    obj = parse("-9223372036854775807").unsafe_object();
    REQUIRE(obj.type() == Object::Type::integer);
    REQUIRE(obj.unsafe_integer() == -9223372036854775807);
}


TEST_CASE("Parse floats", "[parsing]") {
    auto obj = parse("0.0").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("0.").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("0e0").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("0e1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("-1.").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == -1.0);

    obj = parse("1e+1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("1e1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("1e-1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 0.1);

    obj = parse("+1e+1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("+1e1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("+1e-1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == 0.1);

    obj = parse("-1e+1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == -10.0);

    obj = parse("-1e1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == -10.0);

    obj = parse("-1e-1").unsafe_object();
    REQUIRE(obj.type() == Object::Type::floating);
    REQUIRE(obj.unsafe_floating() == -0.1);
}


TEST_CASE("Parse strings", "[parsing]") {
    auto obj = parse("\"\"").unsafe_object();
    REQUIRE(obj.type() == Object::Type::string);
    REQUIRE(obj.unsafe_string() == "");

    obj = parse("\"dingbob\"").unsafe_object();
    REQUIRE(obj.type() == Object::Type::string);
    REQUIRE(obj.unsafe_string() == "dingbob");

    obj = parse("\"ding\\\\bob\"").unsafe_object();
    REQUIRE(obj.type() == Object::Type::string);
    REQUIRE(obj.unsafe_string() == "ding\\bob");

    obj = parse("\"ding\\\"bob\"").unsafe_object();
    REQUIRE(obj.type() == Object::Type::string);
    REQUIRE(obj.unsafe_string() == "ding\"bob");
}


TEST_CASE("Parse lists of atomics", "[parsing]") {
    auto obj = parse("[]").unsafe_list();
    REQUIRE(obj.size() == 0);

    obj = parse("[true]").unsafe_list();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].unsafe_object().type() == Object::Type::boolean);
    REQUIRE(obj[0].unsafe_object().unsafe_boolean() == true);

    obj = parse("[\"\"]").unsafe_list();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].unsafe_object().type() == Object::Type::string);
    REQUIRE(obj[0].unsafe_object().unsafe_string() == "");

    obj = parse("[1, false, -2.3, \"fable\"]").unsafe_list();
    REQUIRE(obj.size() == 4);
    REQUIRE(obj[0].unsafe_object().type() == Object::Type::integer);
    REQUIRE(obj[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_object().type() == Object::Type::boolean);
    REQUIRE(obj[1].unsafe_object().unsafe_boolean() == false);
    REQUIRE(obj[2].unsafe_object().type() == Object::Type::floating);
    REQUIRE(obj[2].unsafe_object().unsafe_floating() == -2.3);
    REQUIRE(obj[3].unsafe_object().type() == Object::Type::string);
    REQUIRE(obj[3].unsafe_object().unsafe_string() == "fable");
}


TEST_CASE("Flexible list parsing", "[parsing]") {
    auto obj = parse("[   ]").unsafe_list();
    REQUIRE(obj.size() == 0);

    obj = parse("[1,]").unsafe_list();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].unsafe_object().unsafe_integer() == 1);

    obj = parse("[  1   ,  ]").unsafe_list();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].unsafe_object().unsafe_integer() == 1);

    obj = parse("[1   ,2  ]").unsafe_list();
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_object().unsafe_integer() == 2);

    obj = parse("[1   ,2  ,]").unsafe_list();
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_object().unsafe_integer() == 2);
}


TEST_CASE("Nested lists", "[parsing]") {
    auto obj = parse("[[]]").unsafe_list();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].type() == AstNode::Type::list);
    REQUIRE(obj[0].unsafe_list().size() == 0);

    obj = parse("[1, [2]]").unsafe_list();
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].type() == AstNode::Type::literal);
    REQUIRE(obj[0].unsafe_object().type() == Object::Type::integer);
    REQUIRE(obj[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj[1].type() == AstNode::Type::list);
    REQUIRE(obj[1].unsafe_list().size() == 1);
    REQUIRE(obj[1].unsafe_list()[0].unsafe_object().type() == Object::Type::integer);
    REQUIRE(obj[1].unsafe_list()[0].unsafe_object().unsafe_integer() == 2);
}


TEST_CASE("Parse map of atomics", "[parsing]") {
    auto obj = parse("{}").unsafe_map();
    REQUIRE(obj.size() == 0);

    obj = parse("{a: 1}").unsafe_map();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].first == "a");
    REQUIRE(obj[0].second.unsafe_object().unsafe_integer() == 1);

    obj = parse("{che9: false}").unsafe_map();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].first == "che9");
    REQUIRE(obj[0].second.unsafe_object().unsafe_boolean() == false);

    obj = parse("{fable: \"fable\"}").unsafe_map();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].first == "fable");
    REQUIRE(obj[0].second.unsafe_object().unsafe_string() == "fable");

    obj = parse("{a: 1, b: true, c: 2.e1, d: \"hoho\"}").unsafe_map();
    REQUIRE(obj.size() == 4);
    REQUIRE(obj[0].first == "a");
    REQUIRE(obj[0].second.unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj[1].first == "b");
    REQUIRE(obj[1].second.unsafe_object().unsafe_boolean() == true);
    REQUIRE(obj[2].first == "c");
    REQUIRE(obj[2].second.unsafe_object().unsafe_floating() == 20.0);
    REQUIRE(obj[3].first == "d");
    REQUIRE(obj[3].second.unsafe_object().unsafe_string() == "hoho");
}


TEST_CASE("Flexible map parsing", "[parsing]") {
    auto obj = parse("{   }").unsafe_map();
    REQUIRE(obj.size() == 0);

    obj = parse("{a:1,}").unsafe_map();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].first == "a");
    REQUIRE(obj[0].second.unsafe_object().unsafe_integer() == 1);

    obj = parse("{  a : 1, }").unsafe_map();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].first == "a");
    REQUIRE(obj[0].second.unsafe_object().unsafe_integer() == 1);

    obj = parse("{a : 1  ,b:2 }").unsafe_map();
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].first == "a");
    REQUIRE(obj[0].second.unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj[1].first == "b");
    REQUIRE(obj[1].second.unsafe_object().unsafe_integer() == 2);
}


TEST_CASE("Nested maps", "[parsing]") {
    auto obj = parse("{a:{}}").unsafe_map();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].first == "a");
    obj = obj[0].second.unsafe_map();
    REQUIRE(obj.size() == 0);

    obj = parse("{a: {b: 1}, c: 2}").unsafe_map();
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].first == "a");
    REQUIRE(obj[1].first == "c");
    REQUIRE(obj[1].second.unsafe_object().unsafe_integer() == 2);
    obj = obj[0].second.unsafe_map();
    REQUIRE(obj.size() == 1);
    REQUIRE(obj[0].first == "b");
    REQUIRE(obj[0].second.unsafe_object().unsafe_integer() == 1);
}


TEST_CASE("Operator expressions", "[parsing]") {
    auto obj = parse("1 + 2").unsafe_opseq();
    REQUIRE(obj.operators.size() == 1);
    REQUIRE(obj.operators[0] == Operator::plus);
    REQUIRE(obj.operands.size() == 2);
    REQUIRE(obj.operands[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj.operands[1].unsafe_object().unsafe_integer() == 2);

    obj = parse("1 / 2 + 3").unsafe_opseq();
    REQUIRE(obj.operators.size() == 1);
    REQUIRE(obj.operators[0] == Operator::plus);
    REQUIRE(obj.operands.size() == 2);
    REQUIRE(obj.operands[1].unsafe_object().unsafe_integer() == 3);
    auto sobj = obj.operands[0].unsafe_opseq();
    REQUIRE(sobj.operators.size() == 1);
    REQUIRE(sobj.operators[0] == Operator::divide);
    REQUIRE(sobj.operands.size() == 2);
    REQUIRE(sobj.operands[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(sobj.operands[1].unsafe_object().unsafe_integer() == 2);

    obj = parse("1 + 2 - 3 * 4 // 5 / 6").unsafe_opseq();
    REQUIRE(obj.operators.size() == 2);
    REQUIRE(obj.operators[0] == Operator::plus);
    REQUIRE(obj.operators[1] == Operator::minus);
    REQUIRE(obj.operands.size() == 3);
    REQUIRE(obj.operands[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(obj.operands[1].unsafe_object().unsafe_integer() == 2);
    sobj = obj.operands[2].unsafe_opseq();
    REQUIRE(sobj.operators.size() == 3);
    REQUIRE(sobj.operators[0] == Operator::multiply);
    REQUIRE(sobj.operators[1] == Operator::integer_divide);
    REQUIRE(sobj.operators[2] == Operator::divide);
    REQUIRE(sobj.operands.size() == 4);
    REQUIRE(sobj.operands[0].unsafe_object().unsafe_integer() == 3);
    REQUIRE(sobj.operands[1].unsafe_object().unsafe_integer() == 4);
    REQUIRE(sobj.operands[2].unsafe_object().unsafe_integer() == 5);
    REQUIRE(sobj.operands[3].unsafe_object().unsafe_integer() == 6);
}
