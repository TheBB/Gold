#include "catch.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold::Ast;


TEST_CASE("Grammar is well-formed", "[parsing]") {
    REQUIRE(analyze_grammar());
}


TEST_CASE("Parse booleans", "[parsing]") {
    auto ast = parse("true");
    REQUIRE(ast->dump() == "Lit(true)");

    ast = parse("false");
    REQUIRE(ast->dump() == "Lit(false)");
}


TEST_CASE("Parse integers", "[parsing]") {
    auto ast = parse("0");
    REQUIRE(ast->dump() == "Lit(0)");

    ast = parse("1");
    REQUIRE(ast->dump() == "Lit(1)");

    ast = parse("+1");
    REQUIRE(ast->dump() == "Lit(1)");

    ast = parse("-1");
    REQUIRE(ast->dump() == "Lit(-1)");

    ast = parse("9223372036854775807");
    REQUIRE(ast->dump() == "Lit(9223372036854775807)");

    ast = parse("-9223372036854775807");
    REQUIRE(ast->dump() == "Lit(-9223372036854775807)");
}


TEST_CASE("Parse floats", "[parsing]") {
    auto ast = parse("0.0");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse("0.");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse("0e0");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse("0e1");
    REQUIRE(ast->dump() == "Lit(0.0)");

    ast = parse("-1.");
    REQUIRE(ast->dump() == "Lit(-1.0)");

    ast = parse("1e+1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse("1e1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse("1e-1");
    REQUIRE(ast->dump() == "Lit(0.1)");

    ast = parse("+1e+1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse("+1e1");
    REQUIRE(ast->dump() == "Lit(10.0)");

    ast = parse("+1e-1");
    REQUIRE(ast->dump() == "Lit(0.1)");

    ast = parse("-1e+1");
    REQUIRE(ast->dump() == "Lit(-10.0)");

    ast = parse("-1e1");
    REQUIRE(ast->dump() == "Lit(-10.0)");

    ast = parse("-1e-1");
    REQUIRE(ast->dump() == "Lit(-0.1)");
}


TEST_CASE("Parse strings", "[parsing]") {
    auto ast = parse("\"\"");
    REQUIRE(ast->dump() == "Lit(\"\")");

    ast = parse("\"dingbob\"");
    REQUIRE(ast->dump() == "Lit(\"dingbob\")");

    ast = parse("\"ding\\\\bob\"");
    REQUIRE(ast->dump() == "Lit(\"ding\\bob\")");

    ast = parse("\"ding\\\"bob\"");
    REQUIRE(ast->dump() == "Lit(\"ding\"bob\")");
}


TEST_CASE("Parse identifiers", "[parsing]") {
    auto ast = parse("dingbob");
    REQUIRE(ast->dump() == "Id(dingbob)");

    // Identifiers that begin with keywords are ok
    ast = parse("ift");
    REQUIRE(ast->dump() == "Id(ift)");

    // But identifiers that ARE keywords aren't
    REQUIRE_THROWS_AS(parse("if"), ParseException);
    REQUIRE_THROWS_AS(parse("then"), ParseException);
    REQUIRE_THROWS_AS(parse("else"), ParseException);
}


TEST_CASE("Parse lists of atomics", "[parsing]") {
    auto ast = parse("[]");
    REQUIRE(ast->dump() == "List()");

    ast = parse("[true]");
    REQUIRE(ast->dump() == "List(Lit(true))");

    ast = parse("[\"\"]");
    REQUIRE(ast->dump() == "List(Lit(\"\"))");

    ast = parse("[1, false, -2.3, \"fable\", lel]");
    REQUIRE(ast->dump() == "List(Lit(1), Lit(false), Lit(-2.3), Lit(\"fable\"), Id(lel))");
}


TEST_CASE("Flexible list parsing", "[parsing]") {
    auto ast = parse("[   ]");
    REQUIRE(ast->dump() == "List()");

    ast = parse("[1,]");
    REQUIRE(ast->dump() == "List(Lit(1))");

    ast = parse("[  1   ,  ]");
    REQUIRE(ast->dump() == "List(Lit(1))");

    ast = parse("[1   ,2  ]");
    REQUIRE(ast->dump() == "List(Lit(1), Lit(2))");

    ast = parse("[1   ,2  ,]");
    REQUIRE(ast->dump() == "List(Lit(1), Lit(2))");
}


TEST_CASE("Nested lists", "[parsing]") {
    auto ast = parse("[[]]");
    REQUIRE(ast->dump() == "List(List())");

    ast = parse("[1, [2]]");
    REQUIRE(ast->dump() == "List(Lit(1), List(Lit(2)))");
}


TEST_CASE("Parse map of atomics", "[parsing]") {
    auto ast = parse("{}");
    REQUIRE(ast->dump() == "Map()");

    ast = parse("{a: 1}");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)))");

    ast = parse("{che9: false}");
    REQUIRE(ast->dump() == "Map(Entry(che9, Lit(false)))");

    ast = parse("{fable: \"fable\"}");
    REQUIRE(ast->dump() == "Map(Entry(fable, Lit(\"fable\")))");

    ast = parse("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: lel}");
    REQUIRE(ast->dump() ==
        "Map(Entry(a, Lit(1)), Entry(b, Lit(true)), "
        "Entry(c, Lit(20.0)), Entry(d, Lit(\"hoho\")), Entry(e, Id(lel)))"
    );
}


TEST_CASE("Flexible map parsing", "[parsing]") {
    auto ast = parse("{   }");
    REQUIRE(ast->dump() == "Map()");

    ast = parse("{a:1,}");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)))");

    ast = parse("{  a : 1, }");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)))");

    ast = parse("{a : 1  ,b:2 }");
    REQUIRE(ast->dump() == "Map(Entry(a, Lit(1)), Entry(b, Lit(2)))");
}


TEST_CASE("Nested maps", "[parsing]") {
    auto ast = parse("{a:{}}");
    REQUIRE(ast->dump() == "Map(Entry(a, Map()))");

    ast = parse("{a: {b: 1}, c: 2}");
    REQUIRE(ast->dump() == "Map(Entry(a, Map(Entry(b, Lit(1)))), Entry(c, Lit(2)))");
}


TEST_CASE("Operator expressions", "[parsing]") {
    auto ast = parse("1 + 2");
    REQUIRE(ast->dump() == "OpSeq(Lit(1) + Lit(2))");

    ast = parse("1 / 2 + 3");
    REQUIRE(ast->dump() == "OpSeq(OpSeq(Lit(1) / Lit(2)) + Lit(3))");

    ast = parse("1 + 2 - 3 * 4 // 5 / 6");
    REQUIRE(ast->dump() ==
        "OpSeq(Lit(1) + Lit(2) - OpSeq("
        "Lit(3) * Lit(4) // Lit(5) / Lit(6)))"
    );
}


TEST_CASE("Parenthesised operator expressions", "[parsing]") {
    auto ast = parse("1 * (2 + 3)");
    REQUIRE(ast->dump() == "OpSeq(Lit(1) * OpSeq(Lit(2) + Lit(3)))");
}


TEST_CASE("Block expressions", "[parsing]") {
    auto ast = parse("{1}");
    REQUIRE(ast->dump() == "Block(Lit(1))");

    ast = parse("{let a = 1 let b = 2 a + b}");
    REQUIRE(ast->dump() == "Block(Entry(a, Lit(1)), Entry(b, Lit(2)), OpSeq(Id(a) + Id(b)))");
}


TEST_CASE("Functions", "[parsing]") {
    auto ast = parse("() => 1");
    REQUIRE(ast->dump() == "Function(Lit(1))");

    ast = parse("(a) => {let b = a b}");
    REQUIRE(ast->dump() == "Function(a, Block(Entry(b, Id(a)), Id(b)))");
}


TEST_CASE("Conditionals", "[parsing]") {
    auto ast = parse("if true then 1 else 2");
    REQUIRE(ast->dump() == "Branch(Lit(true), Lit(1), Lit(2))");
}


TEST_CASE("Function calls", "[parsing]") {
    auto ast = parse("func(1,2,3)");
    REQUIRE(ast->dump() == "FunCall(Id(func), Lit(1), Lit(2), Lit(3))");

    ast = parse("((x,y) => x+y)(1,2)");
    REQUIRE(ast->dump() == "FunCall(Function(x, y, OpSeq(Id(x) + Id(y))), Lit(1), Lit(2))");
}
