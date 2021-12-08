#include "catch.hpp"

#include "gold.hpp"

using namespace Gold;


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


TEST_CASE("Serialization of undefined", "[serialization]") {
    auto val = Object::deserialize(Object::undefined().serialize());
    REQUIRE(val.is_undefined());
}
