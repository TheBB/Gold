#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Grammar is well-formed", "[parsing]") {
    REQUIRE(analyze_grammar());
}


TEST_CASE("Parse booleans", "[parsing]") {
    auto obj = parse("true")->object();
    REQUIRE(obj.type() == Gold::boolean);
    REQUIRE(obj.unsafe_boolean() == true);

    obj = parse("false")->object();
    REQUIRE(obj.type() == Gold::boolean);
    REQUIRE(obj.unsafe_boolean() == false);
}


TEST_CASE("Parse integers", "[parsing]") {
    auto obj = parse("0")->object();
    REQUIRE(obj.type() == Gold::integer);
    REQUIRE(obj.unsafe_integer() == 0);

    obj = parse("1")->object();
    REQUIRE(obj.type() == Gold::integer);
    REQUIRE(obj.unsafe_integer() == 1);

    obj = parse("+1")->object();
    REQUIRE(obj.type() == Gold::integer);
    REQUIRE(obj.unsafe_integer() == 1);

    obj = parse("-1")->object();
    REQUIRE(obj.type() == Gold::integer);
    REQUIRE(obj.unsafe_integer() == -1);

    obj = parse("9223372036854775807")->object();
    REQUIRE(obj.type() == Gold::integer);
    REQUIRE(obj.unsafe_integer() == 9223372036854775807);

    obj = parse("-9223372036854775807")->object();
    REQUIRE(obj.type() == Gold::integer);
    REQUIRE(obj.unsafe_integer() == -9223372036854775807);
}


TEST_CASE("Parse floats", "[parsing]") {
    auto obj = parse("0.0")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("0.")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("0e0")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("0e1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 0.0);

    obj = parse("-1.")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == -1.0);

    obj = parse("1e+1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("1e1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("1e-1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 0.1);

    obj = parse("+1e+1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("+1e1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 10.0);

    obj = parse("+1e-1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == 0.1);

    obj = parse("-1e+1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == -10.0);

    obj = parse("-1e1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == -10.0);

    obj = parse("-1e-1")->object();
    REQUIRE(obj.type() == Gold::floating);
    REQUIRE(obj.unsafe_floating() == -0.1);
}


TEST_CASE("Parse strings", "[parsing]") {
    auto obj = parse("\"\"")->object();
    REQUIRE(obj.type() == Gold::string);
    REQUIRE(obj.unsafe_string() == "");

    obj = parse("\"dingbob\"")->object();
    REQUIRE(obj.type() == Gold::string);
    REQUIRE(obj.unsafe_string() == "dingbob");

    obj = parse("\"ding\\\\bob\"")->object();
    REQUIRE(obj.type() == Gold::string);
    REQUIRE(obj.unsafe_string() == "ding\\bob");

    obj = parse("\"ding\\\"bob\"")->object();
    REQUIRE(obj.type() == Gold::string);
    REQUIRE(obj.unsafe_string() == "ding\"bob");
}
