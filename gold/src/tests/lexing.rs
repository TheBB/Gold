use crate::traits::Taggable;
use crate::lexing::{Lexer, Token};


macro_rules! tok {
    ($x:expr, $tok:expr) => {
        {
            let res = $x;
            assert_eq!(res.as_ref().map(|r| &r.1), Ok(&$tok));
            res.unwrap().0
        }
    };
}


macro_rules! stop {
    ($x:ident) => {
        assert!($x.next_token().is_err())
    };
}


#[test]
fn whitespace() {
    let mut lex = Lexer::new("dingbob");
    lex = tok!(lex.next_token(), Token::Name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("\ndingbob");
    lex = tok!(lex.next_token(), Token::Name("dingbob").tag(1..8).line(2));
    stop!(lex);

    let mut lex = Lexer::new("# this is a comment\ndingbob");
    lex = tok!(lex.next_token(), Token::Name("dingbob").tag(20..27).line(2));
    stop!(lex);

    let mut lex = Lexer::new("dingbob\n#this is a comment");
    lex = tok!(lex.next_token(), Token::Name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("dingbob#this is a comment");
    lex = tok!(lex.next_token(), Token::Name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("# this is a comment\n#a\n#b\ndingbob");
    lex = tok!(lex.next_token(), Token::Name("dingbob").tag(26..33).line(4));
    stop!(lex);
}


#[test]
fn booleans_and_null() {
    let mut lex = Lexer::new("true");
    lex = tok!(lex.next_token(), Token::Name("true").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("false");
    lex = tok!(lex.next_token(), Token::Name("false").tag(0..5));
    stop!(lex);

    let mut lex = Lexer::new("null");
    lex = tok!(lex.next_token(), Token::Name("null").tag(0..4));
    stop!(lex);
}


#[test]
fn floats() {
    let mut lex = Lexer::new("0.0");
    lex = tok!(lex.next_token(), Token::Float("0.0").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("0.");
    lex = tok!(lex.next_token(), Token::Float("0.").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new(".0");
    lex = tok!(lex.next_token(), Token::Float(".0").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new("0e0");
    lex = tok!(lex.next_token(), Token::Float("0e0").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("0e1");
    lex = tok!(lex.next_token(), Token::Float("0e1").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("1.");
    lex = tok!(lex.next_token(), Token::Float("1.").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new("1e+1");
    lex = tok!(lex.next_token(), Token::Float("1e+1").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("1e1");
    lex = tok!(lex.next_token(), Token::Float("1e1").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("1e-1");
    lex = tok!(lex.next_token(), Token::Float("1e-1").tag(0..4));
    stop!(lex);
}


#[test]
fn strings() {
    let mut lex = Lexer::new("\"\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(1));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(8));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob\n");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), Token::Unexpected('\n').tag(8));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob\\\n");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::Unexpected('\n').tag(9));
    stop!(lex);

    let mut lex = Lexer::new("\"ding\\\"bob\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("ding\\\"bob").tag(1..10));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(10));
    stop!(lex);

    let mut lex = Lexer::new("\"ding\\\\bob\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("ding\\\\bob").tag(1..10));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(10));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob$");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), Token::Dollar.tag(8));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob$do");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), Token::Dollar.tag(8));
    lex = tok!(lex.next_token(), Token::Name("do").tag(9..11));
    stop!(lex);

    let mut lex = Lexer::new("\"a + b = $a + $b\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("a + b = ").tag(1..9));
    lex = tok!(lex.next_string(), Token::Dollar.tag(9));
    lex = tok!(lex.next_token(), Token::Name("a").tag(10));
    lex = tok!(lex.next_string(), Token::StringLit(" + ").tag(11..14));
    lex = tok!(lex.next_string(), Token::Dollar.tag(14));
    lex = tok!(lex.next_token(), Token::Name("b").tag(15));
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(16));
    stop!(lex);

    let mut lex = Lexer::new("\"a + b = $a + $b = ${sum}\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("a + b = ").tag(1..9));
    lex = tok!(lex.next_string(), Token::Dollar.tag(9));
    lex = tok!(lex.next_token(), Token::Name("a").tag(10));
    lex = tok!(lex.next_string(), Token::StringLit(" + ").tag(11..14));
    lex = tok!(lex.next_string(), Token::Dollar.tag(14));
    lex = tok!(lex.next_token(), Token::Name("b").tag(15));
    lex = tok!(lex.next_string(), Token::StringLit(" = ").tag(16..19));
    lex = tok!(lex.next_string(), Token::Dollar.tag(19));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(20));
    lex = tok!(lex.next_token(), Token::Name("sum").tag(21..24));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(24));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(25));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob${a}\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), Token::Dollar.tag(8));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(9));
    lex = tok!(lex.next_token(), Token::Name("a").tag(10));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(11));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(12));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob${ a}\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), Token::Dollar.tag(8));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(9));
    lex = tok!(lex.next_token(), Token::Name("a").tag(11));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(12));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(13));
    stop!(lex);

    let mut lex = Lexer::new("\"alpha\" \"bravo\"");
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(0));
    lex = tok!(lex.next_string(), Token::StringLit("alpha").tag(1..6));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(6));
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(8));
    lex = tok!(lex.next_string(), Token::StringLit("bravo").tag(9..14));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(14));
    stop!(lex);
}


#[test]
fn identifiers() {
    let mut lex = Lexer::new("dingbob");
    lex = tok!(lex.next_token(), Token::Name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("lets");
    lex = tok!(lex.next_token(), Token::Name("lets").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("not1");
    lex = tok!(lex.next_token(), Token::Name("not1").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("null1");
    lex = tok!(lex.next_token(), Token::Name("null1").tag(0..5));
    stop!(lex);
}


#[test]
fn lists() {
    let mut lex = Lexer::new("[]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(1));
    stop!(lex);

    let mut lex = Lexer::new("[   ]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(4));
    stop!(lex);

    let mut lex = Lexer::new("[true]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::Name("true").tag(1..5));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(5));
    stop!(lex);

    let mut lex = Lexer::new("[\"\"]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(1));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(2));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(3));
    stop!(lex);

    let mut lex = Lexer::new("[1,]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(1));
    lex = tok!(lex.next_token(), Token::Comma.tag(2));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(3));
    stop!(lex);

    let mut lex = Lexer::new("[1, false, 2.3, \"fable\", lel]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(1));
    lex = tok!(lex.next_token(), Token::Comma.tag(2));
    lex = tok!(lex.next_token(), Token::Name("false").tag(4..9));
    lex = tok!(lex.next_token(), Token::Comma.tag(9));
    lex = tok!(lex.next_token(), Token::Float("2.3").tag(11..14));
    lex = tok!(lex.next_token(), Token::Comma.tag(14));
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(16));
    lex = tok!(lex.next_string(), Token::StringLit("fable").tag(17..22));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(22));
    lex = tok!(lex.next_token(), Token::Comma.tag(23));
    lex = tok!(lex.next_token(), Token::Name("lel").tag(25..28));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(28));
    stop!(lex);

    let mut lex = Lexer::new("[1, ...x, y]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(1));
    lex = tok!(lex.next_token(), Token::Comma.tag(2));
    lex = tok!(lex.next_token(), Token::Ellipsis.tag(4..7));
    lex = tok!(lex.next_token(), Token::Name("x").tag(7));
    lex = tok!(lex.next_token(), Token::Comma.tag(8));
    lex = tok!(lex.next_token(), Token::Name("y").tag(10));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(11));
    stop!(lex);

    let mut lex = Lexer::new("[1, for x in y: x, 2]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(1));
    lex = tok!(lex.next_token(), Token::Comma.tag(2));
    lex = tok!(lex.next_token(), Token::Name("for").tag(4..7));
    lex = tok!(lex.next_token(), Token::Name("x").tag(8));
    lex = tok!(lex.next_token(), Token::Name("in").tag(10..12));
    lex = tok!(lex.next_token(), Token::Name("y").tag(13));
    lex = tok!(lex.next_token(), Token::Colon.tag(14));
    lex = tok!(lex.next_token(), Token::Name("x").tag(16));
    lex = tok!(lex.next_token(), Token::Comma.tag(17));
    lex = tok!(lex.next_token(), Token::Integer("2").tag(19));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(20));
    stop!(lex);

    let mut lex = Lexer::new("[when f(x): x]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::Name("when").tag(1..5));
    lex = tok!(lex.next_token(), Token::Name("f").tag(6));
    lex = tok!(lex.next_token(), Token::OpenParen.tag(7));
    lex = tok!(lex.next_token(), Token::Name("x").tag(8));
    lex = tok!(lex.next_token(), Token::CloseParen.tag(9));
    lex = tok!(lex.next_token(), Token::Colon.tag(10));
    lex = tok!(lex.next_token(), Token::Name("x").tag(12));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(13));
    stop!(lex);

    let mut lex = Lexer::new("[[]]");
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(0));
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(1));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(2));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(3));
    stop!(lex);
}


#[test]
fn maps() {
    let mut lex = Lexer::new("{}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::CloseBrace.tag(1)));
    stop!(lex);

    let mut lex = Lexer::new("{  }");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (3, Token::CloseBrace.tag(3)));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Name("a").tag(1)));
    lex = tok!(lex.next_token(), Token::Colon.tag(2));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(4));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(5));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1,}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Name("a").tag(1)));
    lex = tok!(lex.next_token(), Token::Colon.tag(2));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(4));
    lex = tok!(lex.next_token(), Token::Comma.tag(5));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(6));
    stop!(lex);

    let mut lex = Lexer::new("{che9: false}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Name("che9").tag(1..5)));
    lex = tok!(lex.next_token(), Token::Colon.tag(5));
    lex = tok!(lex.next_token(), Token::Name("false").tag(7..12));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(12));
    stop!(lex);

    let mut lex = Lexer::new("{fable: \"fable\"}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Name("fable").tag(1..6)));
    lex = tok!(lex.next_token(), Token::Colon.tag(6));
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(8));
    lex = tok!(lex.next_string(), Token::StringLit("fable").tag(9..14));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(14));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(15));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Name("a").tag(1)));
    lex = tok!(lex.next_token(), Token::Colon.tag(2));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(4));
    lex = tok!(lex.next_token(), Token::Comma.tag(5));
    lex = tok!(lex.next_key(), (7, Token::Name("b").tag(7)));
    lex = tok!(lex.next_token(), Token::Colon.tag(8));
    lex = tok!(lex.next_token(), Token::Name("true").tag(10..14));
    lex = tok!(lex.next_token(), Token::Comma.tag(14));
    lex = tok!(lex.next_key(), (16, Token::Name("c").tag(16)));
    lex = tok!(lex.next_token(), Token::Colon.tag(17));
    lex = tok!(lex.next_token(), Token::Float("2.e1").tag(19..23));
    lex = tok!(lex.next_token(), Token::Comma.tag(23));
    lex = tok!(lex.next_key(), (25, Token::Name("d").tag(25)));
    lex = tok!(lex.next_token(), Token::Colon.tag(26));
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(28));
    lex = tok!(lex.next_string(), Token::StringLit("hoho").tag(29..33));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(33));
    lex = tok!(lex.next_token(), Token::Comma.tag(34));
    lex = tok!(lex.next_key(), (36, Token::Name("e").tag(36)));
    lex = tok!(lex.next_token(), Token::Colon.tag(37));
    lex = tok!(lex.next_token(), Token::Float("1e1").tag(39..42));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(42));
    stop!(lex);

    let mut lex = Lexer::new("{ident-with-hyphen: 1}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Name("ident-with-hyphen").tag(1..18)));
    lex = tok!(lex.next_token(), Token::Colon.tag(18));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(20));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(21));
    stop!(lex);

    let mut lex = Lexer::new("{$z: y}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Dollar.tag(1)));
    lex = tok!(lex.next_token(), Token::Name("z").tag(2));
    lex = tok!(lex.next_token(), Token::Colon.tag(3));
    lex = tok!(lex.next_token(), Token::Name("y").tag(5));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(6));
    stop!(lex);

    let mut lex = Lexer::new("{$\"z\": y}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Dollar.tag(1)));
    lex = tok!(lex.next_token(), Token::DoubleQuote.tag(2));
    lex = tok!(lex.next_string(), Token::StringLit("z").tag(3));
    lex = tok!(lex.next_string(), Token::DoubleQuote.tag(4));
    lex = tok!(lex.next_token(), Token::Colon.tag(5));
    lex = tok!(lex.next_token(), Token::Name("y").tag(7));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(8));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z:: here's some text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (3, Token::Name("z").tag(5).line(2)));
    lex = tok!(lex.next_token(), Token::DoubleComma.tag(6..8).line(2));
    lex = tok!(lex.next_multistring(3), Token::MultiString(" here's some text\n").tag(8..26).line(2));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(26).line(3));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z:: here's some\n",
        "       text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (3, Token::Name("z").tag(5).line(2)));
    lex = tok!(lex.next_token(), Token::DoubleComma.tag(6..8).line(2));
    lex = tok!(lex.next_multistring(3), Token::MultiString(" here's some\n       text\n").tag(8..33).line(2));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(33).line(4));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z:: here's some\n",
        "     text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (3, Token::Name("z").tag(5).line(2)));
    lex = tok!(lex.next_token(), Token::DoubleComma.tag(6..8).line(2));
    lex = tok!(lex.next_multistring(3), Token::MultiString(" here's some\n     text\n").tag(8..31).line(2));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(31).line(4));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "     here's some\n",
        "     text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (3, Token::Name("z").tag(5).line(2)));
    lex = tok!(lex.next_token(), Token::DoubleComma.tag(6..8).line(2));
    lex = tok!(lex.next_multistring(3), Token::MultiString("\n     here's some\n     text\n").tag(8..36).line(2));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(36).line(5));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "     here's some\n",
        "       text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (3, Token::Name("z").tag(5).line(2)));
    lex = tok!(lex.next_token(), Token::DoubleComma.tag(6..8).line(2));
    lex = tok!(lex.next_multistring(3), Token::MultiString("\n     here's some\n       text\n").tag(8..38).line(2));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(38).line(5));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "       here's some\n",
        "     text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (3, Token::Name("z").tag(5).line(2)));
    lex = tok!(lex.next_token(), Token::DoubleComma.tag(6..8).line(2));
    lex = tok!(lex.next_multistring(3), Token::MultiString("\n       here's some\n     text\n").tag(8..38).line(2));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(38).line(5));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "    a:: x\n",
        "    b: y,\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (4, Token::Name("a").tag(6).line(2)));
    lex = tok!(lex.next_token(), Token::DoubleComma.tag(7..9).line(2));
    lex = tok!(lex.next_multistring(4), Token::MultiString(" x\n").tag(9..12).line(2));
    lex = tok!(lex.next_key(), (4, Token::Name("b").tag(16).line(3)));
    lex = tok!(lex.next_token(), Token::Colon.tag(17).line(3));
    lex = tok!(lex.next_token(), Token::Name("y").tag(19).line(3));
    lex = tok!(lex.next_token(), Token::Comma.tag(20).line(3));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(22).line(4));
    stop!(lex);

    let mut lex = Lexer::new("{...y, x: 1}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Ellipsis.tag(1..4)));
    lex = tok!(lex.next_token(), Token::Name("y").tag(4));
    lex = tok!(lex.next_token(), Token::Comma.tag(5));
    lex = tok!(lex.next_key(), (7, Token::Name("x").tag(7)));
    lex = tok!(lex.next_token(), Token::Colon.tag(8));
    lex = tok!(lex.next_token(), Token::Integer("1").tag(10));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(11));
    stop!(lex);

    let mut lex = Lexer::new("{for [x,y] in z: x: y}");
    lex = tok!(lex.next_token(), Token::OpenBrace.tag(0));
    lex = tok!(lex.next_key(), (1, Token::Name("for").tag(1..4)));
    lex = tok!(lex.next_token(), Token::OpenBracket.tag(5));
    lex = tok!(lex.next_token(), Token::Name("x").tag(6));
    lex = tok!(lex.next_token(), Token::Comma.tag(7));
    lex = tok!(lex.next_token(), Token::Name("y").tag(8));
    lex = tok!(lex.next_token(), Token::CloseBracket.tag(9));
    lex = tok!(lex.next_token(), Token::Name("in").tag(11..13));
    lex = tok!(lex.next_token(), Token::Name("z").tag(14));
    lex = tok!(lex.next_token(), Token::Colon.tag(15));
    lex = tok!(lex.next_key(), (17, Token::Name("x").tag(17)));
    lex = tok!(lex.next_token(), Token::Colon.tag(18));
    lex = tok!(lex.next_token(), Token::Name("y").tag(20));
    lex = tok!(lex.next_token(), Token::CloseBrace.tag(21));
    stop!(lex);
}
