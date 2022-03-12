#include "catch.hpp"

#include "gold.hpp"

using namespace Gold;


TEST_CASE("Basic methods", "[object]") {
    REQUIRE(Object::null().type() == Object::Type::null);
    REQUIRE(Object::null().type_name() == "null");
    REQUIRE(Object::null().is_null() == true);

    REQUIRE(Object::integer(1).type() == Object::Type::integer);
    REQUIRE(Object::integer(1).type_name() == "integer");
    REQUIRE(Object::integer(1).is_null() == false);
    REQUIRE(Object::integer(1).unsafe_integer() == 1);

    REQUIRE(Object::string("a").type() == Object::Type::string);
    REQUIRE(Object::string("a").type_name() == "string");
    REQUIRE(Object::string("a").is_null() == false);
    REQUIRE(Object::string("a").unsafe_string() == "a");

    REQUIRE(Object::boolean(true).type() == Object::Type::boolean);
    REQUIRE(Object::boolean(true).type_name() == "boolean");
    REQUIRE(Object::boolean(true).is_null() == false);
    REQUIRE(Object::boolean(true).unsafe_boolean() == true);

    REQUIRE(Object::floating(1.2).type() == Object::Type::floating);
    REQUIRE(Object::floating(1.2).type_name() == "floating");
    REQUIRE(Object::floating(1.2).is_null() == false);
    REQUIRE(Object::floating(1.2).unsafe_floating() == 1.2);

    Object::MapT map {{"a", Object::integer(1)}};
    REQUIRE(Object::map(map).type() == Object::Type::map);
    REQUIRE(Object::map(map).type_name() == "map");
    REQUIRE(Object::map(map).is_null() == false);
    REQUIRE(*Object::map(map).unsafe_map() == map);

    Object::ListT list {Object::integer(1)};
    REQUIRE(Object::list(list).type() == Object::Type::list);
    REQUIRE(Object::list(list).type_name() == "list");
    REQUIRE(Object::list(list).is_null() == false);
    REQUIRE(*Object::list(list).unsafe_list() == list);

    REQUIRE(evaluate_string("() => 1").type() == Object::Type::function);
    REQUIRE(evaluate_string("() => 1").type_name() == "function");

    REQUIRE(evaluate_string("int").type() == Object::Type::function);
    REQUIRE(evaluate_string("int").type_name() == "function");
}


TEST_CASE("Dump", "[object]") {
    REQUIRE(Object::null().dump() == "null");
    REQUIRE(Object::string("abc\b\f\n\r\t\"\\").dump() == "\"abc\\b\\f\\n\\r\\t\\\"\\\\\"");
    REQUIRE(Object::boolean(true).dump() == "true");
    REQUIRE(Object::boolean(false).dump() == "false");
    REQUIRE(Object::list({
        Object::integer(1),
        Object::integer(2)
    }).dump() == "[1, 2]");
    REQUIRE(Object::map({
        {"a", Object::integer(1)},
        {"b", Object::integer(2)}
    }).dump() == "{a: 1, b: 2}");
}
