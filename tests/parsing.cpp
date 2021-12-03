#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Grammar is well-formed", "[parsing]") {
    REQUIRE(analyze_grammar());
}


TEST_CASE("Parse booleans", "[parsing]") {
    auto ast = parse("true");
    REQUIRE(ast.unsafe_object().type() == Object::Type::boolean);
    REQUIRE(ast.unsafe_object().unsafe_boolean() == true);

    ast = parse("false");
    REQUIRE(ast.unsafe_object().type() == Object::Type::boolean);
    REQUIRE(ast.unsafe_object().unsafe_boolean() == false);
}


TEST_CASE("Parse integers", "[parsing]") {
    auto ast = parse("0");
    REQUIRE(ast.unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_object().unsafe_integer() == 0);

    ast = parse("1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_object().unsafe_integer() == 1);

    ast = parse("+1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_object().unsafe_integer() == 1);

    ast = parse("-1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_object().unsafe_integer() == -1);

    ast = parse("9223372036854775807");
    REQUIRE(ast.unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_object().unsafe_integer() == 9223372036854775807);

    ast = parse("-9223372036854775807");
    REQUIRE(ast.unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_object().unsafe_integer() == -9223372036854775807);
}


TEST_CASE("Parse floats", "[parsing]") {
    auto ast = parse("0.0");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 0.0);

    ast = parse("0.");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 0.0);

    ast = parse("0e0");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 0.0);

    ast = parse("0e1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 0.0);

    ast = parse("-1.");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == -1.0);

    ast = parse("1e+1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 10.0);

    ast = parse("1e1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 10.0);

    ast = parse("1e-1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 0.1);

    ast = parse("+1e+1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 10.0);

    ast = parse("+1e1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 10.0);

    ast = parse("+1e-1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == 0.1);

    ast = parse("-1e+1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == -10.0);

    ast = parse("-1e1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == -10.0);

    ast = parse("-1e-1");
    REQUIRE(ast.unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_object().unsafe_floating() == -0.1);
}


TEST_CASE("Parse strings", "[parsing]") {
    auto ast = parse("\"\"");
    REQUIRE(ast.unsafe_object().type() == Object::Type::string);
    REQUIRE(ast.unsafe_object().unsafe_string() == "");

    ast = parse("\"dingbob\"");
    REQUIRE(ast.unsafe_object().type() == Object::Type::string);
    REQUIRE(ast.unsafe_object().unsafe_string() == "dingbob");

    ast = parse("\"ding\\\\bob\"");
    REQUIRE(ast.unsafe_object().type() == Object::Type::string);
    REQUIRE(ast.unsafe_object().unsafe_string() == "ding\\bob");

    ast = parse("\"ding\\\"bob\"");
    REQUIRE(ast.unsafe_object().type() == Object::Type::string);
    REQUIRE(ast.unsafe_object().unsafe_string() == "ding\"bob");
}


TEST_CASE("Parse lists of atomics", "[parsing]") {
    auto ast = parse("[]");
    REQUIRE(ast.unsafe_list().size() == 0);

    ast = parse("[true]");
    REQUIRE(ast.unsafe_list().size() == 1);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().type() == Object::Type::boolean);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_boolean() == true);

    ast = parse("[\"\"]");
    REQUIRE(ast.unsafe_list().size() == 1);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().type() == Object::Type::string);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_string() == "");

    ast = parse("[1, false, -2.3, \"fable\"]");
    REQUIRE(ast.unsafe_list().size() == 4);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_list()[1].unsafe_object().type() == Object::Type::boolean);
    REQUIRE(ast.unsafe_list()[1].unsafe_object().unsafe_boolean() == false);
    REQUIRE(ast.unsafe_list()[2].unsafe_object().type() == Object::Type::floating);
    REQUIRE(ast.unsafe_list()[2].unsafe_object().unsafe_floating() == -2.3);
    REQUIRE(ast.unsafe_list()[3].unsafe_object().type() == Object::Type::string);
    REQUIRE(ast.unsafe_list()[3].unsafe_object().unsafe_string() == "fable");
}


TEST_CASE("Flexible list parsing", "[parsing]") {
    auto ast = parse("[   ]");
    REQUIRE(ast.unsafe_list().size() == 0);

    ast = parse("[1,]");
    REQUIRE(ast.unsafe_list().size() == 1);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_integer() == 1);

    ast = parse("[  1   ,  ]");
    REQUIRE(ast.unsafe_list().size() == 1);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_integer() == 1);

    ast = parse("[1   ,2  ]");
    REQUIRE(ast.unsafe_list().size() == 2);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_list()[1].unsafe_object().unsafe_integer() == 2);

    ast = parse("[1   ,2  ,]");
    REQUIRE(ast.unsafe_list().size() == 2);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_list()[1].unsafe_object().unsafe_integer() == 2);
}


TEST_CASE("Nested lists", "[parsing]") {
    auto ast = parse("[[]]");
    REQUIRE(ast.unsafe_list().size() == 1);
    REQUIRE(ast.unsafe_list()[0].type() == AstNode::Type::list);
    REQUIRE(ast.unsafe_list()[0].unsafe_list().size() == 0);

    ast = parse("[1, [2]]");
    REQUIRE(ast.unsafe_list().size() == 2);
    REQUIRE(ast.unsafe_list()[0].type() == AstNode::Type::literal);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_list()[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_list()[1].type() == AstNode::Type::list);
    REQUIRE(ast.unsafe_list()[1].unsafe_list().size() == 1);
    REQUIRE(ast.unsafe_list()[1].unsafe_list()[0].unsafe_object().type() == Object::Type::integer);
    REQUIRE(ast.unsafe_list()[1].unsafe_list()[0].unsafe_object().unsafe_integer() == 2);
}


TEST_CASE("Parse map of atomics", "[parsing]") {
    auto ast = parse("{}");
    REQUIRE(ast.unsafe_map().size() == 0);

    ast = parse("{a: 1}");
    REQUIRE(ast.unsafe_map().size() == 1);
    REQUIRE(ast.unsafe_map()[0].first == "a");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_object().unsafe_integer() == 1);

    ast = parse("{che9: false}");
    REQUIRE(ast.unsafe_map().size() == 1);
    REQUIRE(ast.unsafe_map()[0].first == "che9");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_object().unsafe_boolean() == false);

    ast = parse("{fable: \"fable\"}");
    REQUIRE(ast.unsafe_map().size() == 1);
    REQUIRE(ast.unsafe_map()[0].first == "fable");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_object().unsafe_string() == "fable");

    ast = parse("{a: 1, b: true, c: 2.e1, d: \"hoho\"}");
    REQUIRE(ast.unsafe_map().size() == 4);
    REQUIRE(ast.unsafe_map()[0].first == "a");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_map()[1].first == "b");
    REQUIRE(ast.unsafe_map()[1].second.unsafe_object().unsafe_boolean() == true);
    REQUIRE(ast.unsafe_map()[2].first == "c");
    REQUIRE(ast.unsafe_map()[2].second.unsafe_object().unsafe_floating() == 20.0);
    REQUIRE(ast.unsafe_map()[3].first == "d");
    REQUIRE(ast.unsafe_map()[3].second.unsafe_object().unsafe_string() == "hoho");
}


TEST_CASE("Flexible map parsing", "[parsing]") {
    auto ast = parse("{   }");
    REQUIRE(ast.unsafe_map().size() == 0);

    ast = parse("{a:1,}");
    REQUIRE(ast.unsafe_map().size() == 1);
    REQUIRE(ast.unsafe_map()[0].first == "a");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_object().unsafe_integer() == 1);

    ast = parse("{  a : 1, }");
    REQUIRE(ast.unsafe_map().size() == 1);
    REQUIRE(ast.unsafe_map()[0].first == "a");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_object().unsafe_integer() == 1);

    ast = parse("{a : 1  ,b:2 }");
    REQUIRE(ast.unsafe_map().size() == 2);
    REQUIRE(ast.unsafe_map()[0].first == "a");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_map()[1].first == "b");
    REQUIRE(ast.unsafe_map()[1].second.unsafe_object().unsafe_integer() == 2);
}


TEST_CASE("Nested maps", "[parsing]") {
    auto ast = parse("{a:{}}");
    REQUIRE(ast.unsafe_map().size() == 1);
    REQUIRE(ast.unsafe_map()[0].first == "a");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_map().size() == 0);

    ast = parse("{a: {b: 1}, c: 2}");
    REQUIRE(ast.unsafe_map().size() == 2);
    REQUIRE(ast.unsafe_map()[0].first == "a");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_map().size() == 1);
    REQUIRE(ast.unsafe_map()[0].second.unsafe_map()[0].first == "b");
    REQUIRE(ast.unsafe_map()[0].second.unsafe_map()[0].second.unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_map()[1].first == "c");
    REQUIRE(ast.unsafe_map()[1].second.unsafe_object().unsafe_integer() == 2);
}


TEST_CASE("Operator expressions", "[parsing]") {
    auto ast = parse("1 + 2");
    REQUIRE(ast.unsafe_opseq().operators.size() == 1);
    REQUIRE(ast.unsafe_opseq().operators[0] == Operator::plus);
    REQUIRE(ast.unsafe_opseq().operands.size() == 2);
    REQUIRE(ast.unsafe_opseq().operands[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_opseq().operands[1].unsafe_object().unsafe_integer() == 2);

    ast = parse("1 / 2 + 3");
    REQUIRE(ast.unsafe_opseq().operators.size() == 1);
    REQUIRE(ast.unsafe_opseq().operators[0] == Operator::plus);
    REQUIRE(ast.unsafe_opseq().operands.size() == 2);
    REQUIRE(ast.unsafe_opseq().operands[1].unsafe_object().unsafe_integer() == 3);
    REQUIRE(ast.unsafe_opseq().operands[0].unsafe_opseq().operators.size() == 1);
    REQUIRE(ast.unsafe_opseq().operands[0].unsafe_opseq().operators[0] == Operator::divide);
    REQUIRE(ast.unsafe_opseq().operands[0].unsafe_opseq().operands.size() == 2);
    REQUIRE(ast.unsafe_opseq().operands[0].unsafe_opseq().operands[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_opseq().operands[0].unsafe_opseq().operands[1].unsafe_object().unsafe_integer() == 2);

    ast = parse("1 + 2 - 3 * 4 // 5 / 6");
    REQUIRE(ast.unsafe_opseq().operators.size() == 2);
    REQUIRE(ast.unsafe_opseq().operators[0] == Operator::plus);
    REQUIRE(ast.unsafe_opseq().operators[1] == Operator::minus);
    REQUIRE(ast.unsafe_opseq().operands.size() == 3);
    REQUIRE(ast.unsafe_opseq().operands[0].unsafe_object().unsafe_integer() == 1);
    REQUIRE(ast.unsafe_opseq().operands[1].unsafe_object().unsafe_integer() == 2);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operators.size() == 3);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operators[0] == Operator::multiply);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operators[1] == Operator::integer_divide);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operators[2] == Operator::divide);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operands.size() == 4);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operands[0].unsafe_object().unsafe_integer() == 3);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operands[1].unsafe_object().unsafe_integer() == 4);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operands[2].unsafe_object().unsafe_integer() == 5);
    REQUIRE(ast.unsafe_opseq().operands[2].unsafe_opseq().operands[3].unsafe_object().unsafe_integer() == 6);
}
