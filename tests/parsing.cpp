#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Parse booleans", "[parsing]") {
    auto obj = parse("true")->object();
    REQUIRE(obj.type() == Gold::boolean);
    REQUIRE(obj.unsafe_boolean() == true);

    obj = parse("false")->object();
    REQUIRE(obj.type() == Gold::boolean);
    REQUIRE(obj.unsafe_boolean() == false);
}
