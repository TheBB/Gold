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
