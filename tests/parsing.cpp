#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


TEST_CASE("Grammar is well-formed", "[parsing]") {
    REQUIRE(analyze_grammar());
}


TEST_CASE("Parse booleans", "[parsing]") {
    auto ast = parse_string("true");
    REQUIRE(ast->dump() == "Lit(true)");

    ast = parse_string("false");
    REQUIRE(ast->dump() == "Lit(false)");
}


TEST_CASE("Parse integers", "[parsing]") {
    auto ast = parse_string("0");
    REQUIRE(ast->dump() == "Lit(0)");

    ast = parse_string("1");
    REQUIRE(ast->dump() == "Lit(1)");

    ast = parse_string("+1");
    REQUIRE(ast->dump() == "Lit(1)");

    ast = parse_string("-1");
    REQUIRE(ast->dump() == "Lit(-1)");

    ast = parse_string("9223372036854775807");
    REQUIRE(ast->dump() == "Lit(9223372036854775807)");

    ast = parse_string("-9223372036854775808");
    REQUIRE(ast->dump() == "Lit(-9223372036854775808)");
}


TEST_CASE("Parse floats", "[parsing]") {
    auto ast = parse_string("0.0");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse_string("0.");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse_string(".0");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse_string("0e0");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse_string("0e1");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse_string("-1.");
    REQUIRE(ast->dump() == "Lit(-1.0)");

    ast = parse_string("1e+1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse_string("1e1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse_string("1e-1");
    REQUIRE(ast->dump() == "Lit(0.1)");

    ast = parse_string("+1e+1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse_string("+1e1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse_string("+1e-1");
    REQUIRE(ast->dump() == "Lit(0.1)");

    ast = parse_string("-1e+1");
    REQUIRE(ast->dump() == "Lit(-10.0)");

    ast = parse_string("-1e1");
    REQUIRE(ast->dump() == "Lit(-10.0)");

    ast = parse_string("-1e-1");
    REQUIRE(ast->dump() == "Lit(-0.1)");
}


TEST_CASE("Parse strings", "[parsing]") {
    auto ast = parse_string("\"\"");
    REQUIRE(ast->dump() == "Lit(\"\")");

    ast = parse_string("\"dingbob\"");
    REQUIRE(ast->dump() == "Lit(\"dingbob\")");

    ast = parse_string("\"ding\\\\bob\"");
    REQUIRE(ast->dump() == "Lit(\"ding\\bob\")");

    ast = parse_string("\"ding\\\"bob\"");
    REQUIRE(ast->dump() == "Lit(\"ding\"bob\")");
}


TEST_CASE("Parse identifiers", "[parsing]") {
    auto ast = parse_string("dingbob");
    REQUIRE(ast->dump() == "Id(dingbob)");

    ast = parse_string("nullt");
    REQUIRE(ast->dump() == "Id(nullt)");

    ast = parse_string("truet");
    REQUIRE(ast->dump() == "Id(truet)");

    ast = parse_string("falset");
    REQUIRE(ast->dump() == "Id(falset)");

    // Identifiers that begin with keywords are ok
    ast = parse_string("ift");
    REQUIRE(ast->dump() == "Id(ift)");

    // But identifiers that ARE keywords aren't
    REQUIRE_THROWS_AS(parse_string("if"), ParseException);
    REQUIRE_THROWS_AS(parse_string("then"), ParseException);
    REQUIRE_THROWS_AS(parse_string("else"), ParseException);
}


TEST_CASE("Parse null", "[parsing]") {
    auto ast = parse_string("null");
    REQUIRE(ast->dump() == "Lit(null)");
}


TEST_CASE("Parse lists of atomics", "[parsing]") {
    auto ast = parse_string("[]");
    REQUIRE(ast->dump() == "List()");

    ast = parse_string("[true]");
    REQUIRE(ast->dump() == "List(Lit(true))");

    ast = parse_string("[\"\"]");
    REQUIRE(ast->dump() == "List(Lit(\"\"))");

    ast = parse_string("[1, false, -2.3, \"fable\", lel]");
    REQUIRE(ast->dump() == "List(Lit(1), Lit(false), Lit(-2.3), Lit(\"fable\"), Id(lel))");
}


TEST_CASE("Flexible list parsing", "[parsing]") {
    auto ast = parse_string("[   ]");
    REQUIRE(ast->dump() == "List()");

    ast = parse_string("[1,]");
    REQUIRE(ast->dump() == "List(Lit(1))");

    ast = parse_string("[  1   ,  ]");
    REQUIRE(ast->dump() == "List(Lit(1))");

    ast = parse_string("[1   ,2  ]");
    REQUIRE(ast->dump() == "List(Lit(1), Lit(2))");

    ast = parse_string("[1   ,2  ,]");
    REQUIRE(ast->dump() == "List(Lit(1), Lit(2))");
}


TEST_CASE("Nested lists", "[parsing]") {
    auto ast = parse_string("[[]]");
    REQUIRE(ast->dump() == "List(List())");

    ast = parse_string("[1, [2]]");
    REQUIRE(ast->dump() == "List(Lit(1), List(Lit(2)))");
}


TEST_CASE("Parse map of atomics", "[parsing]") {
    auto ast = parse_string("{}");
    REQUIRE(ast->dump() == "Map()");

    ast = parse_string("{a: 1}");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)))");

    ast = parse_string("{che9: false}");
    REQUIRE(ast->dump() == "Map(Entry(che9, Lit(false)))");

    ast = parse_string("{fable: \"fable\"}");
    REQUIRE(ast->dump() == "Map(Entry(fable, Lit(\"fable\")))");

    ast = parse_string("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: lel}");
    REQUIRE(ast->dump() ==
        "Map(Entry(a, Lit(1)), Entry(b, Lit(true)), "
        "Entry(c, Lit(20.0)), Entry(d, Lit(\"hoho\")), Entry(e, Id(lel)))"
    );
}


TEST_CASE("Flexible map parsing", "[parsing]") {
    auto ast = parse_string("{   }");
    REQUIRE(ast->dump() == "Map()");

    ast = parse_string("{a:1,}");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)))");

    ast = parse_string("{  a : 1, }");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)))");

    ast = parse_string("{a : 1  ,b:2 }");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)), Entry(b, Lit(2)))");
}


TEST_CASE("Nested maps", "[parsing]") {
    auto ast = parse_string("{a:{}}");
    REQUIRE(ast->dump() == "Map(Entry(a, Map()))");

    ast = parse_string("{a: {b: 1}, c: 2}");
    REQUIRE(ast->dump() == "Map(Entry(a, Map(Entry(b, Lit(1)))), Entry(c, Lit(2)))");
}


TEST_CASE("Operator expressions", "[parsing]") {
    auto ast = parse_string("1 + 2");
    REQUIRE(ast->dump() == "BinOp(Lit(1) + Lit(2))");

    ast = parse_string("1 / 2 + 3");
    REQUIRE(ast->dump() == "BinOp(BinOp(Lit(1) / Lit(2)) + Lit(3))");

    ast = parse_string("1 + 2 - 3 * 4 // 5 / 6");
    REQUIRE(ast->dump() ==
        "BinOp(Lit(1) + BinOp(Lit(2) - BinOp(Lit(3) "
        "* BinOp(Lit(4) // BinOp(Lit(5) / Lit(6))))))"
    );
}


TEST_CASE("Parenthesised operator expressions", "[parsing]") {
    auto ast = parse_string("1 * (2 + 3)");
    REQUIRE(ast->dump() == "BinOp(Lit(1) * BinOp(Lit(2) + Lit(3)))");
}


TEST_CASE("Block expressions", "[parsing]") {
    auto ast = parse_string("{1}");
    REQUIRE(ast->dump() == "Block(Lit(1))");

    ast = parse_string("{let a = 1 let b = 2 a + b}");
    REQUIRE(ast->dump() == "Block(Entry(a, Lit(1)), Entry(b, Lit(2)), BinOp(Id(a) + Id(b)))");
}


TEST_CASE("Functions", "[parsing]") {
    auto ast = parse_string("() => 1");
    REQUIRE(ast->dump() == "Function(Lit(1))");

    ast = parse_string("(a) => {let b = a b}");
    REQUIRE(ast->dump() == "Function(a, Block(Entry(b, Id(a)), Id(b)))");
}


TEST_CASE("Conditionals", "[parsing]") {
    auto ast = parse_string("if true then 1 else 2");
    REQUIRE(ast->dump() == "Branch(Lit(true), Lit(1), Lit(2))");
}


TEST_CASE("Postfix operators", "[parsing]") {
    auto ast = parse_string("func(1,2,3)");
    REQUIRE(ast->dump() == "FunCall(Id(func), Lit(1), Lit(2), Lit(3))");

    ast = parse_string("((x,y) => x+y)(1,2)");
    REQUIRE(ast->dump() == "FunCall(Function(x, y, BinOp(Id(x) + Id(y))), Lit(1), Lit(2))");

    ast = parse_string("abc.def");
    REQUIRE(ast->dump() == "Index(Id(abc), Lit(\"def\"))");

    ast = parse_string("f(a).x");
    REQUIRE(ast->dump() == "Index(FunCall(Id(f), Id(a)), Lit(\"x\"))");

    ast = parse_string("f.x(a)");
    REQUIRE(ast->dump() == "FunCall(Index(Id(f), Lit(\"x\")), Id(a))");

    ast = parse_string("dingbob[\"roflmao\"]");
    REQUIRE(ast->dump() == "Index(Id(dingbob), Lit(\"roflmao\"))");
}


TEST_CASE("File parsing as block", "[parsing]") {
    auto ast = parse_string("let a = 1\na", false);
    REQUIRE(ast->dump() == "Block(Entry(a, Lit(1)), Id(a))");
}
