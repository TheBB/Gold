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
