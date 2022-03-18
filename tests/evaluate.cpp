#include "catch.hpp"

#include "gold.hpp"

using Catch::Matchers::Contains;
using namespace Gold;


TEST_CASE("Evaluating literals", "[evaluate]") {
    REQUIRE(evaluate_string("1").unsafe_integer() == 1);
    REQUIRE(evaluate_string("-1").unsafe_integer() == -1);
    REQUIRE(evaluate_string("+1").unsafe_integer() == 1);
    REQUIRE(evaluate_string("true").unsafe_boolean() == true);
    REQUIRE(evaluate_string("false").unsafe_boolean() == false);
    REQUIRE(evaluate_string("null").is_null());
    REQUIRE(evaluate_string("2.").unsafe_floating() == 2.0);
    REQUIRE(evaluate_string("1.2").unsafe_floating() == 1.2);
    REQUIRE(evaluate_string("-3e1").unsafe_floating() == -30.0);
    REQUIRE(evaluate_string("+4e-1").unsafe_floating() == 0.4);
    REQUIRE(evaluate_string("5e+1").unsafe_floating() == 50.0);

    REQUIRE(evaluate_string("\"\"").unsafe_string() == "");
    REQUIRE(evaluate_string("\"dingbob\"").unsafe_string() == "dingbob");
    REQUIRE(evaluate_string("\"ding\\\"bob\"").unsafe_string() == "ding\"bob");
    REQUIRE(evaluate_string("\"ding\\\\bob\"").unsafe_string() == "ding\\bob");

    REQUIRE(evaluate_string("\"\\u0021\"").unsafe_string() == "!");
    REQUIRE(evaluate_string("\"\\u004c\"").unsafe_string() == "L");
    REQUIRE(evaluate_string("\"\\u006D\"").unsafe_string() == "m");

    REQUIRE(evaluate_string("\"\\b\\f\\n\\r\\t\"").unsafe_string() == "\b\f\n\r\t");
}


TEST_CASE("Evaluating lists", "[evaluate]") {
    auto obj = evaluate_string("[]");
    REQUIRE(obj.type() == Object::Type::list);
    REQUIRE(obj.size() == 0);

    obj = evaluate_string("[1, false, \"dingbob\", 2.2, null]");
    REQUIRE(obj.type() == Object::Type::list);
    REQUIRE(obj.size() == 5);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_boolean() == false);
    REQUIRE(obj[2].unsafe_string() == "dingbob");
    REQUIRE(obj[3].unsafe_floating() == 2.2);
    REQUIRE(obj[4].is_null());
}


TEST_CASE("Evaluating maps", "[evaluate]") {
    auto obj = evaluate_string("{}");
    REQUIRE(obj.size() == 0);

    obj = evaluate_string("{a: -1, b: true, c: \"\", d: 3.14, e: null}");
    REQUIRE(obj.size() == 5);
    REQUIRE(obj["a"].unsafe_integer() == -1);
    REQUIRE(obj["b"].unsafe_boolean() == true);
    REQUIRE(obj["c"].unsafe_string() == "");
    REQUIRE(obj["d"].unsafe_floating() == 3.14);
    REQUIRE(obj["e"].is_null());
}


TEST_CASE("Maps with evaluated keys", "[evaluate]") {
    auto obj = evaluate_string("let a = \"hi\" in {$a: 1}");
    REQUIRE(obj.size() == 1);
    REQUIRE(obj["hi"].unsafe_integer() == 1);

    obj = evaluate_string("let f = (x) => \"${x}${x}\" in {$f(\"yo\"): 1}");
    REQUIRE(obj.size() == 1);
    REQUIRE(obj["yoyo"].unsafe_integer() == 1);
}


TEST_CASE("Blocks and bindings", "[evaluate]") {
    auto obj = evaluate_string(
        "let a = 1\n"
        "in a"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let a = 2.1\n"
        "let b = \"zomg\"\n"
        "in [a, b]"
    );
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_floating() == 2.1);
    REQUIRE(obj[1].unsafe_string() == "zomg");

    obj = evaluate_string(
        "let a = 2.1\n"
        "let b = a\n"
        "in b"
    );
    REQUIRE(obj.unsafe_floating() == 2.1);

    obj = evaluate_string(
        "let a = 1\n"
        "let b = let a = 2 in a\n"
        "in [a, b]"
    );
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);

    obj = evaluate_string(
        "let a = 1\n"
        "let b = a\n"
        "let a = 2\n"
        "in [a, b]"
    );
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 2);
    REQUIRE(obj[1].unsafe_integer() == 1);
}


TEST_CASE("Arithmetic", "[evaluate]") {
    REQUIRE(evaluate_string("1 + 2").unsafe_integer() == 3);
    REQUIRE(evaluate_string("3 + 2").unsafe_integer() == 5);
    REQUIRE(evaluate_string("3 + 2 - 5").unsafe_integer() == 0);
    REQUIRE(evaluate_string("3 - -5").unsafe_integer() == 8);
    REQUIRE(evaluate_string("2 * 4").unsafe_integer() == 8);
    REQUIRE(evaluate_string("2.0 * 4").unsafe_floating() == 8.0);
    REQUIRE(evaluate_string("2 * 4.0").unsafe_floating() == 8.0);
    REQUIRE(evaluate_string("2.0 * 4.0").unsafe_floating() == 8.0);
    REQUIRE(evaluate_string("2 * 4 + 1").unsafe_integer() == 9);
    REQUIRE(evaluate_string("2 * (4 + 1)").unsafe_integer() == 10);
    REQUIRE(evaluate_string("3 / 2").unsafe_floating() == 1.5);
    REQUIRE(evaluate_string("3.0 / 2").unsafe_floating() == 1.5);
    REQUIRE(evaluate_string("3 / 2.0").unsafe_floating() == 1.5);
    REQUIRE(evaluate_string("3.0 / 2.0").unsafe_floating() == 1.5);
    REQUIRE(evaluate_string("3 // 2").unsafe_integer() == 1);
    REQUIRE(evaluate_string("1 + 2.0").unsafe_floating() == 3.0);
    REQUIRE(evaluate_string("1.0 + 2").unsafe_floating() == 3.0);
    REQUIRE(evaluate_string("1.0 + 2.0").unsafe_floating() == 3.0);
    REQUIRE(evaluate_string("1.0 - 2.0").unsafe_floating() == -1.0);
    REQUIRE(evaluate_string("1.0 - 2").unsafe_floating() == -1.0);
    REQUIRE(evaluate_string("1 - 2.0").unsafe_floating() == -1.0);
    REQUIRE(evaluate_string("1 - 2 + 3").unsafe_integer() == 2);
    REQUIRE(evaluate_string("2 // 2 * 2").unsafe_integer() == 2);
}


TEST_CASE("Comparison", "[evaluate]") {
    REQUIRE(evaluate_string("1 < 2").unsafe_boolean() == true);
    REQUIRE(evaluate_string("1 < 2.0").unsafe_boolean() == true);
    REQUIRE(evaluate_string("1.0 < 2").unsafe_boolean() == true);
    REQUIRE(evaluate_string("1.0 < 2.0").unsafe_boolean() == true);
    REQUIRE(evaluate_string("\"a\" < \"b\"").unsafe_boolean() == true);
    REQUIRE(evaluate_string("1 > 2").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1.0 > 2").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1 > 2.0").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1.0 > 2.0").unsafe_boolean() == false);
    REQUIRE(evaluate_string("\"a\" > \"b\"").unsafe_boolean() == false);
    REQUIRE(evaluate_string("2 <= 2").unsafe_boolean() == true);
    REQUIRE(evaluate_string("2.0 <= 2").unsafe_boolean() == true);
    REQUIRE(evaluate_string("2 <= 2.0").unsafe_boolean() == true);
    REQUIRE(evaluate_string("2.0 <= 2.0").unsafe_boolean() == true);
    REQUIRE(evaluate_string("\"a\" <= \"b\"").unsafe_boolean() == true);
    REQUIRE(evaluate_string("1 >= 2").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1.0 >= 2").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1 >= 2.0").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1.0 >= 2.0").unsafe_boolean() == false);
    REQUIRE(evaluate_string("\"a\" >= \"b\"").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1 == 2").unsafe_boolean() == false);
    REQUIRE(evaluate_string("2 == 2").unsafe_boolean() == true);
    REQUIRE(evaluate_string("2.0 == 2.0").unsafe_boolean() == true);
    REQUIRE(evaluate_string("2 == 2.0").unsafe_boolean() == true);
    REQUIRE(evaluate_string("2.0 == 2").unsafe_boolean() == true);
    REQUIRE(evaluate_string("\"a\" == \"b\"").unsafe_boolean() == false);
    REQUIRE(evaluate_string("true == false").unsafe_boolean() == false);
    REQUIRE(evaluate_string("null == null").unsafe_boolean() == true);
    REQUIRE(evaluate_string("{} == {}").unsafe_boolean() == true);
    REQUIRE(evaluate_string("{a: 1} == {a: 1}").unsafe_boolean() == true);
    REQUIRE(evaluate_string("{a: 2} == {a: 1}").unsafe_boolean() == false);
    REQUIRE(evaluate_string("{a: 1} == {a: 1, b: 1}").unsafe_boolean() == false);
    REQUIRE(evaluate_string("{a: 1} == {a: 1, a: 1}").unsafe_boolean() == true);
    REQUIRE(evaluate_string("[] == []").unsafe_boolean() == true);
    REQUIRE(evaluate_string("[1] == []").unsafe_boolean() == false);
    REQUIRE(evaluate_string("[1] == [2]").unsafe_boolean() == false);
    REQUIRE(evaluate_string("[1] == [1]").unsafe_boolean() == true);
    REQUIRE(evaluate_string("[] == {}").unsafe_boolean() == false);
    REQUIRE(evaluate_string("1 != 2").unsafe_boolean() == true);
    REQUIRE(evaluate_string("2 != 2").unsafe_boolean() == false);
}


TEST_CASE("Logic", "[evaluate]") {
    REQUIRE(evaluate_string("true and 1").unsafe_integer() == 1);
    REQUIRE(evaluate_string("false and 1").unsafe_boolean() == false);
    REQUIRE(evaluate_string("true or 1").unsafe_boolean() == true);
    REQUIRE(evaluate_string("false or 1").unsafe_integer() == 1);
    REQUIRE(evaluate_string("null or 1").unsafe_integer() == 1);
    REQUIRE(evaluate_string("1 or 1").unsafe_integer() == 1);
}


TEST_CASE("List concatenation", "[evaluate]") {
    auto obj = evaluate_string("[1, 2] + [3]");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);
    REQUIRE(obj[2].unsafe_integer() == 3);
}


TEST_CASE("Evaluation of functions", "[evaluate]") {
    auto obj = evaluate_string(
        "let double = (x) => x + x\n"
        "let applytwice = (f,x) => f(f(x))\n"
        "in applytwice(double, [1])"
    );
    REQUIRE(obj.size() == 4);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 1);
    REQUIRE(obj[2].unsafe_integer() == 1);
    REQUIRE(obj[3].unsafe_integer() == 1);

    obj = evaluate_string(
        "let a = 1\n"
        "let b = () => a\n"
        "let a = 2\n"
        "in b()"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let a = 1\n"
        "let b = (q = a) => q\n"
        "in b()"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let a = 1\n"
        "let b = (q = a) => q\n"
        "in b(2)"
    );
    REQUIRE(obj.unsafe_integer() == 2);

    obj = evaluate_string(
        "let b = () => let a = 1 in (q = a) => q\n"
        "let c = b()\n"
        "in c()"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let a = (q, ...) => q\n"
        "in a(1, 2, 3)"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let a = (q, ...x) => [q, ...x]\n"
        "in a(1, 2, 3)"
    );
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);
    REQUIRE(obj[2].unsafe_integer() == 3);

    obj = evaluate_string(
        "let a = (q, p = q) => p\n"
        "in a(1, 2)"
    );
    REQUIRE(obj.unsafe_integer() == 2);

    obj = evaluate_string(
        "let a = (q, p = q) => p\n"
        "in a(1)"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("() => q");
    REQUIRE(obj.type() == Object::Type::function);
}


TEST_CASE("Subscripting", "[evaluate]") {
    REQUIRE(evaluate_string("[1,2,3][0]").unsafe_integer() == 1);
    REQUIRE(evaluate_string("{a: 1, b: 2}.a").unsafe_integer() == 1);
    REQUIRE(evaluate_string("{a: 1, b: 2}[\"a\"]").unsafe_integer() == 1);
}


TEST_CASE("Splatting", "[evaluate]") {
    auto obj = evaluate_string("[1, ...[2, 3], 4]");
    REQUIRE(obj.size() == 4);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);
    REQUIRE(obj[2].unsafe_integer() == 3);
    REQUIRE(obj[3].unsafe_integer() == 4);

    obj = evaluate_string("{a: 1, ...{b: 2, c: 3}, d: 4}");
    REQUIRE(obj.size() == 4);
    REQUIRE(obj["a"].unsafe_integer() == 1);
    REQUIRE(obj["b"].unsafe_integer() == 2);
    REQUIRE(obj["c"].unsafe_integer() == 3);
    REQUIRE(obj["d"].unsafe_integer() == 4);

    obj = evaluate_string("{a: 1, ...{a: 2, c: 3}, c: 4}");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["a"].unsafe_integer() == 2);
    REQUIRE(obj["c"].unsafe_integer() == 4);
}


TEST_CASE("Branching in collections", "[evaluate]") {
    auto obj = evaluate_string("[if true then 1 else 2, 3]");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 3);

    obj = evaluate_string("[if false then 1 else 2, 3]");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 2);
    REQUIRE(obj[1].unsafe_integer() == 3);
}


TEST_CASE("Conditional collection elements", "[evaluate]") {
    auto obj = evaluate_string("[if true: 1, if false: 2, if true then 3 else 4, 5]");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 3);
    REQUIRE(obj[2].unsafe_integer() == 5);

    obj = evaluate_string("{a: if true then 1 else 2, if true: b: 3, if false: c: 4}");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["a"].unsafe_integer() == 1);
    REQUIRE(obj["b"].unsafe_integer() == 3);
}


TEST_CASE("Looped collection elements", "[evaluate]") {
    auto obj = evaluate_string("let a = [1, 2, 3] in [for x in a: x + 1]");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0].unsafe_integer() == 2);
    REQUIRE(obj[1].unsafe_integer() == 3);
    REQUIRE(obj[2].unsafe_integer() == 4);

    obj = evaluate_string("{for [x,y] in [[\"a\",1], [\"b\",2]]: $x: y}");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["a"].unsafe_integer() == 1);
    REQUIRE(obj["b"].unsafe_integer() == 2);
}


TEST_CASE("Complex collection elements", "[evaluate]") {
    auto obj = evaluate_string(
        "let a = [1, 2, 3, 4, 5]\n"
        "in [for x in a: if x < 3: x]"
    );
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);

    obj = evaluate_string(
        "let a = [[1], [2, 3], [4, 5, 6]]\n"
        "in [for x in a: if len(x) > 1: ...x]"
    );
    REQUIRE(obj.size() == 5);
    REQUIRE(obj[0].unsafe_integer() == 2);
    REQUIRE(obj[1].unsafe_integer() == 3);
    REQUIRE(obj[2].unsafe_integer() == 4);
    REQUIRE(obj[3].unsafe_integer() == 5);
    REQUIRE(obj[4].unsafe_integer() == 6);

    obj = evaluate_string(
        "let a = [[\"x\",1], [\"y\",2], [\"z\",3]]\n"
        "in {for [x,y] in a: if y != 2: $x: y}"
    );
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["x"].unsafe_integer() == 1);
    REQUIRE(obj["z"].unsafe_integer() == 3);
}


TEST_CASE("List bindings", "[evaluate]") {
    auto obj = evaluate_string("let [a,b] = [1,2] in {a: a, b: b}");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["a"].unsafe_integer() == 1);
    REQUIRE(obj["b"].unsafe_integer() == 2);

    obj = evaluate_string("let [a,[b]] = [1,[2]] in {a: a, b: b}");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["a"].unsafe_integer() == 1);
    REQUIRE(obj["b"].unsafe_integer() == 2);

    obj = evaluate_string("let [a, ...] = [1] in a");
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("let [a, ...] = [1, 2, 3] in a");
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("let [a, ...b] = [1, 2, 3] in b[0]");
    REQUIRE(obj.unsafe_integer() == 2);

    obj = evaluate_string("let [a, ...b] = [1] in b");
    REQUIRE(obj.size() == 0);

    obj = evaluate_string("let [a, b = 1, ...c] = [2] in [a, b, c]");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0].unsafe_integer() == 2);
    REQUIRE(obj[1].unsafe_integer() == 1);
    REQUIRE(obj[2].size() == 0);
}


TEST_CASE("Map bindings", "[evaluate]") {
    auto obj = evaluate_string("let {a: a, b: b} = {a: 1, b: 2} in {a: a, b: b}");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["a"].unsafe_integer() == 1);
    REQUIRE(obj["b"].unsafe_integer() == 2);

    obj = evaluate_string("let {a: {b: b}} = {a: {b: 1}} in b");
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("let {a: a} = {a: 1} in a");
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("let {a: a} = {a: 1, b: 2, c: 3} in a");
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("let {a: a, ...b} = {a: 1, b: 2, c: 3} in b");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj["b"].unsafe_integer() == 2);
    REQUIRE(obj["c"].unsafe_integer() == 3);

    obj = evaluate_string("let {a: a, ...b} = {a: 1} in b");
    REQUIRE(obj.size() == 0);

    obj = evaluate_string("let {a, b} = {a: 1, b: 2} in [a, b]");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);

    obj = evaluate_string("let {a, b} = {a: 1, b: 2, c: 3} in [a, b]");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);

    obj = evaluate_string("let {a = 1} = {} in a");
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("let {a: q = 1} = {} in q");
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string("let {a = let {b = 2} = {} in b} = {} in a");
    REQUIRE(obj.unsafe_integer() == 2);
}


TEST_CASE("Function bindings", "[evaluate]") {
    auto obj = evaluate_string(
        "let a = (x, [y, z]) => x + y + z\n"
        "in a(1, [2, 3])"
    );
    REQUIRE(obj.unsafe_integer() == 6);

    obj = evaluate_string(
        "let f = ([y = 1]) => y\n"
        "in f([])"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let q = 1\n"
        "let f = ([y = q]) => y\n"
        "in f([])"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let f = (q) => ([y = q]) => y\n"
        "let q = 1\n"
        "in f(2)([])"
    );
    REQUIRE(obj.unsafe_integer() == 2);

    obj = evaluate_string(
        "let f = (x, {y, z}) => x + y + z\n"
        "in f(1, {y: 2, z: 3})"
    );
    REQUIRE(obj.unsafe_integer() == 6);

    obj = evaluate_string(
        "let f = (x, {y, z}) => x + y + z\n"
        "in f(1, y: 2, z: 3)"
    );
    REQUIRE(obj.unsafe_integer() == 6);

    obj = evaluate_string(
        "let f = ({y = 1}) => y\n"
        "in f({})"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let q = 1\n"
        "let f = ({y = q}) => y\n"
        "in f({})"
    );
    REQUIRE(obj.unsafe_integer() == 1);

    obj = evaluate_string(
        "let f = (q) => ({y = q}) => y\n"
        "let q = 1\n"
        "in f(2)({})"
    );
    REQUIRE(obj.unsafe_integer() == 2);
}


TEST_CASE("Builtins", "[evalute]") {
    REQUIRE(evaluate_string("len([])").unsafe_integer() == 0);
    REQUIRE(evaluate_string("len([1,2,3])").unsafe_integer() == 3);
    REQUIRE(evaluate_string("len({})").unsafe_integer() == 0);
    REQUIRE(evaluate_string("len({a: 1, b: 2})").unsafe_integer() == 2);

    auto obj = evaluate_string("range(3)");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0].unsafe_integer() == 0);
    REQUIRE(obj[1].unsafe_integer() == 1);
    REQUIRE(obj[2].unsafe_integer() == 2);

    obj = evaluate_string("range(1, 3)");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);

    obj = evaluate_string("map((x) => x+1, range(3))");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0].unsafe_integer() == 1);
    REQUIRE(obj[1].unsafe_integer() == 2);
    REQUIRE(obj[2].unsafe_integer() == 3);

    obj = evaluate_string("filter((x) => x<=3, range(5))");
    REQUIRE(obj.size() == 4);
    REQUIRE(obj[0].unsafe_integer() == 0);
    REQUIRE(obj[1].unsafe_integer() == 1);
    REQUIRE(obj[2].unsafe_integer() == 2);
    REQUIRE(obj[3].unsafe_integer() == 3);

    obj = evaluate_string("items({a: 1, b: 2})");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0].size() == 2);
    REQUIRE(obj[0][0].unsafe_string() == "a");
    REQUIRE(obj[0][1].unsafe_integer() == 1);
    REQUIRE(obj[1].size() == 2);
    REQUIRE(obj[1][0].unsafe_string() == "b");
    REQUIRE(obj[1][1].unsafe_integer() == 2);
}


TEST_CASE("Type conversion", "[evaluate]") {
    REQUIRE(evaluate_string("int(1)").unsafe_integer() == 1);
    REQUIRE(evaluate_string("int(true)").unsafe_integer() == 1);
    REQUIRE(evaluate_string("int(false)").unsafe_integer() == 0);
    REQUIRE(evaluate_string("int(1.2)").unsafe_integer() == 1);
    REQUIRE(evaluate_string("int(-1.2)").unsafe_integer() == -1);
    REQUIRE(evaluate_string("int(\"-3\")").unsafe_integer() == -3);
    REQUIRE(evaluate_string("bool(1)").unsafe_boolean() == true);
    REQUIRE(evaluate_string("bool(0)").unsafe_boolean() == false);
    REQUIRE(evaluate_string("bool(1.5)").unsafe_boolean() == true);
    REQUIRE(evaluate_string("bool(0.0)").unsafe_boolean() == false);
    REQUIRE(evaluate_string("bool(true)").unsafe_boolean() == true);
    REQUIRE(evaluate_string("bool(false)").unsafe_boolean() == false);
    REQUIRE(evaluate_string("bool(null)").unsafe_boolean() == false);
    REQUIRE(evaluate_string("bool([])").unsafe_boolean() == true);
    REQUIRE(evaluate_string("str(1)").unsafe_string() == "1");
    REQUIRE(evaluate_string("str(1.2)").unsafe_string() == "1.2");
    REQUIRE(evaluate_string("str(\"delta\")").unsafe_string() == "delta");
    REQUIRE(evaluate_string("str(true)").unsafe_string() == "true");
    REQUIRE(evaluate_string("str(false)").unsafe_string() == "false");
    REQUIRE(evaluate_string("str(null)").unsafe_string() == "null");
    REQUIRE(evaluate_string("float(1)").unsafe_floating() == 1.0);
    REQUIRE(evaluate_string("float(1.0)").unsafe_floating() == 1.0);
    REQUIRE(evaluate_string("float(true)").unsafe_floating() == 1.0);
    REQUIRE(evaluate_string("float(false)").unsafe_floating() == 0.0);
    REQUIRE(evaluate_string("float(\"1.2\")").unsafe_floating() == 1.2);
}


TEST_CASE("Import", "[evaluate]") {
    REQUIRE(evaluate_string("import(\"std\").version").unsafe_string() == "0.1.0");
}


TEST_CASE("Errors", "[evaluate]") {
    // Look-up non-existing binding
    REQUIRE_THROWS_WITH(evaluate_string("q"), Contains("1:1"));
    REQUIRE_THROWS_WITH(evaluate_string("(() => q)()"), Contains("1:8") && Contains("1:10"));

    // Binding fails to match
    REQUIRE_THROWS_WITH(evaluate_string("let [a] = 1 in a"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("let [] = [1] in 1"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("let [a, ...] = [] in a"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("let [[a]] = [1] in a"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("let {a} = 1 in a"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("let {a} = {} in a"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("let {a: [q]} = {a: 1} in q"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("[for [[a]] in [1]: a]"), Contains("1:6"));
    REQUIRE_THROWS_WITH(evaluate_string("{for [[a]] in [1]: b: a}"), Contains("1:6"));

    // Splatting wrong type
    REQUIRE_THROWS_WITH(evaluate_string("[...1]"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("[for x in 1: x]"), Contains("1:11"));
    REQUIRE_THROWS_WITH(evaluate_string("{...1}"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("{for x in 1: a: x}"), Contains("1:11"));

    // Branching on non-boolean
    REQUIRE_THROWS_WITH(evaluate_string("[if 1: 1]"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("{if 1: a: 1}"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("if 1 then 2 else 3"), Contains("1:4"));

    // Maps without strings as keys
    REQUIRE_THROWS_WITH(evaluate_string("{$1: 1}"), Contains("1:3"));

    // Binary operations
    REQUIRE_THROWS_WITH(evaluate_string("1 + f"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("1 + []"), Contains("1:3"));
    REQUIRE_THROWS_WITH(evaluate_string("1 - []"), Contains("1:3"));
    REQUIRE_THROWS_WITH(evaluate_string("true * 1.2"), Contains("1:6"));
    REQUIRE_THROWS_WITH(evaluate_string("{} / []"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("{} // []"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("{} < []"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("{} > []"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("{} <= []"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("{} >= []"), Contains("1:4"));

    // Postfix operators on wrong types
    REQUIRE_THROWS_WITH(evaluate_string("1()"), Contains("1:2"));
    REQUIRE_THROWS_WITH(evaluate_string("1[1]"), Contains("1:2"));
    REQUIRE_THROWS_WITH(evaluate_string("1[true]"), Contains("1:2"));
    REQUIRE_THROWS_WITH(evaluate_string("(() => 1[1])()"), Contains("1:9"));

    // Indexing errors
    REQUIRE_THROWS_WITH(evaluate_string("[][1]"), Contains("1:3"));
    REQUIRE_THROWS_WITH(evaluate_string("[][-1]"), Contains("1:3"));
    REQUIRE_THROWS_WITH(evaluate_string("{}[null]"), Contains("1:3"));
    REQUIRE_THROWS_WITH(evaluate_string("null.a"), Contains("1:5"));
    REQUIRE_THROWS_WITH(evaluate_string("{}.a"), Contains("1:3"));

    // Calling with wrong number of arguments
    REQUIRE_THROWS_WITH(evaluate_string("(() => 1)(1)"), Contains("1:10"));
    REQUIRE_THROWS_WITH(evaluate_string("((a) => 1)()"), Contains("1:11"));

    // Builtins
    REQUIRE_THROWS_WITH(evaluate_string("len(null)"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("range(true)"), Contains("1:6"));
    REQUIRE_THROWS_WITH(evaluate_string("import(\"at\")"), Contains("1:7"));
    REQUIRE_THROWS_WITH(evaluate_string("import(true)"), Contains("1:7"));

    // Illegal type conversions
    REQUIRE_THROWS_WITH(evaluate_string("int([])"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("float([])"), Contains("1:6"));
    REQUIRE_THROWS_WITH(evaluate_string("str([])"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("map((x) => 1, true)"), Contains("1:4"));
    REQUIRE_THROWS_WITH(evaluate_string("filter((x) => x > 1, null)"), Contains("1:7"));
    REQUIRE_THROWS_WITH(evaluate_string("items([])"), Contains("1:6"));
    REQUIRE_THROWS_WITH(evaluate_string("import([])"), Contains("1:7"));
}
