use crate::error::Tagged;
use crate::traits::Taggable;
use crate::lexing::{Lexer, Token};


fn lex(code: &str) -> Vec<Tagged<Token>> {
    Lexer::new(code).collect()
}


#[test]
fn whitespace() {
    assert_eq!(lex("dingbob"), vec![
        Token::Name("dingbob").tag(0..7),
    ]);

    assert_eq!(lex("\ndingbob"), vec![
        Token::Name("dingbob").tag(1..8).line(2),
    ]);

    assert_eq!(lex("# this is a comment\ndingbob"), vec![
        Token::Name("dingbob").tag(20..27).line(2),
    ]);

    assert_eq!(lex("dingbob\n# this is a comment"), vec![
        Token::Name("dingbob").tag(0..7),
    ]);

    assert_eq!(lex("# this is a comment\n#a\n#b\ndingbob"), vec![
        Token::Name("dingbob").tag(26..33).line(4),
    ]);
}


#[test]
fn booleans_and_null() {
    assert_eq!(lex("true"), vec![
        Token::Name("true").tag(0..4),
    ]);

    assert_eq!(lex("false"), vec![
        Token::Name("false").tag(0..5),
    ]);

    assert_eq!(lex("null"), vec![
        Token::Name("null").tag(0..4),
    ]);
}


#[test]
fn floats() {
    assert_eq!(lex("0.0"), vec![
        Token::Float("0.0").tag(0..3),
    ]);

    assert_eq!(lex("0."), vec![
        Token::Float("0.").tag(0..2),
    ]);

    assert_eq!(lex(".0"), vec![
        Token::Float(".0").tag(0..2),
    ]);

    assert_eq!(lex("0e0"), vec![
        Token::Float("0e0").tag(0..3),
    ]);

    assert_eq!(lex("0e1"), vec![
        Token::Float("0e1").tag(0..3),
    ]);

    assert_eq!(lex("1."), vec![
        Token::Float("1.").tag(0..2),
    ]);

    assert_eq!(lex("1e+1"), vec![
        Token::Float("1e+1").tag(0..4),
    ]);

    assert_eq!(lex("1e1"), vec![
        Token::Float("1e1").tag(0..3),
    ]);

    assert_eq!(lex("1e-1"), vec![
        Token::Float("1e-1").tag(0..4),
    ]);
}


#[test]
fn strings() {
    assert_eq!(lex("\"\""), vec![
        Token::DoubleQuote.tag(0),
        Token::DoubleQuote.tag(1),
    ]);

    assert_eq!(lex("\"dingbob\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("dingbob").tag(1..8),
        Token::DoubleQuote.tag(8),
    ]);

    assert_eq!(lex("\"dingbob"), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("dingbob").tag(1..8),
    ]);

    assert_eq!(lex("\"dingbob\n\""), vec![
        Token::DoubleQuote.tag(0),
        Token::Unexpected('\n').tag(8),
    ]);

    assert_eq!(lex("\"dingbob\\\n\""), vec![
        Token::DoubleQuote.tag(0),
        Token::Unexpected('\n').tag(9),
    ]);

    assert_eq!(lex("\"ding\\\"bob\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("ding\\\"bob").tag(1..10),
        Token::DoubleQuote.tag(10),
    ]);

    assert_eq!(lex("\"ding\\\\bob\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("ding\\\\bob").tag(1..10),
        Token::DoubleQuote.tag(10),
    ]);

    assert_eq!(lex("\"dingbob$"), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("dingbob").tag(1..8),
        Token::Dollar.tag(8),
    ]);

    assert_eq!(lex("\"dingbob$do"), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("dingbob").tag(1..8),
        Token::Dollar.tag(8),
        Token::Name("do").tag(9..11),
    ]);

    assert_eq!(lex("\"a + b = $a + $b\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("a + b = ").tag(1..9),
        Token::Dollar.tag(9),
        Token::Name("a").tag(10),
        Token::StringLit(" + ").tag(11..14),
        Token::Dollar.tag(14),
        Token::Name("b").tag(15),
        Token::DoubleQuote.tag(16),
    ]);

    assert_eq!(lex("\"a + b = $a + $b = ${sum}\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("a + b = ").tag(1..9),
        Token::Dollar.tag(9),
        Token::Name("a").tag(10),
        Token::StringLit(" + ").tag(11..14),
        Token::Dollar.tag(14),
        Token::Name("b").tag(15),
        Token::StringLit(" = ").tag(16..19),
        Token::Dollar.tag(19),
        Token::OpenBrace.tag(20),
        Token::Name("sum").tag(21..24),
        Token::CloseBrace.tag(24),
        Token::DoubleQuote.tag(25),
    ]);

    assert_eq!(lex("\"dingbob${a}\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("dingbob").tag(1..8),
        Token::Dollar.tag(8),
        Token::OpenBrace.tag(9),
        Token::Name("a").tag(10),
        Token::CloseBrace.tag(11),
        Token::DoubleQuote.tag(12),
    ]);

    assert_eq!(lex("\"dingbob${ a}\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("dingbob").tag(1..8),
        Token::Dollar.tag(8),
        Token::OpenBrace.tag(9),
        Token::Name("a").tag(11),
        Token::CloseBrace.tag(12),
        Token::DoubleQuote.tag(13),
    ]);

    assert_eq!(lex("\"alpha\" \"bravo\""), vec![
        Token::DoubleQuote.tag(0),
        Token::StringLit("alpha").tag(1..6),
        Token::DoubleQuote.tag(6),
        Token::DoubleQuote.tag(8),
        Token::StringLit("bravo").tag(9..14),
        Token::DoubleQuote.tag(14),
    ]);
}


#[test]
fn identifiers() {
    assert_eq!(lex("dingbob"), vec![
        Token::Name("dingbob").tag(0..7),
    ]);

    assert_eq!(lex("lets"), vec![
        Token::Name("lets").tag(0..4),
    ]);

    assert_eq!(lex("not1"), vec![
        Token::Name("not1").tag(0..4),
    ]);
}


#[test]
fn lists() {
    assert_eq!(lex("[]"), vec![
        Token::OpenBracket.tag(0),
        Token::CloseBracket.tag(1),
    ]);

    assert_eq!(lex("[   ]"), vec![
        Token::OpenBracket.tag(0),
        Token::CloseBracket.tag(4),
    ]);

    assert_eq!(lex("[true]"), vec![
        Token::OpenBracket.tag(0),
        Token::Name("true").tag(1..5),
        Token::CloseBracket.tag(5),
    ]);

    assert_eq!(lex("[\"\"]"), vec![
        Token::OpenBracket.tag(0),
        Token::DoubleQuote.tag(1),
        Token::DoubleQuote.tag(2),
        Token::CloseBracket.tag(3),
    ]);

    assert_eq!(lex("[1,]"), vec![
        Token::OpenBracket.tag(0),
        Token::Integer("1").tag(1),
        Token::Comma.tag(2),
        Token::CloseBracket.tag(3),
    ]);

    assert_eq!(lex("[1, false, 2.3, \"fable\", lel]"), vec![
        Token::OpenBracket.tag(0),
        Token::Integer("1").tag(1),
        Token::Comma.tag(2),
        Token::Name("false").tag(4..9),
        Token::Comma.tag(9),
        Token::Float("2.3").tag(11..14),
        Token::Comma.tag(14),
        Token::DoubleQuote.tag(16),
        Token::StringLit("fable").tag(17..22),
        Token::DoubleQuote.tag(22),
        Token::Comma.tag(23),
        Token::Name("lel").tag(25..28),
        Token::CloseBracket.tag(28),
    ]);

    assert_eq!(lex("[1, ...x, y]"), vec![
        Token::OpenBracket.tag(0),
        Token::Integer("1").tag(1),
        Token::Comma.tag(2),
        Token::Ellipsis.tag(4..7),
        Token::Name("x").tag(7),
        Token::Comma.tag(8),
        Token::Name("y").tag(10),
        Token::CloseBracket.tag(11),
    ]);

    assert_eq!(lex("[1, for x in y: x, 2]"), vec![
        Token::OpenBracket.tag(0),
        Token::Integer("1").tag(1),
        Token::Comma.tag(2),
        Token::Name("for").tag(4..7),
        Token::Name("x").tag(8),
        Token::Name("in").tag(10..12),
        Token::Name("y").tag(13),
        Token::Colon.tag(14),
        Token::Name("x").tag(16),
        Token::Comma.tag(17),
        Token::Integer("2").tag(19),
        Token::CloseBracket.tag(20),
    ]);

    assert_eq!(lex("[when f(x): x]"), vec![
        Token::OpenBracket.tag(0),
        Token::Name("when").tag(1..5),
        Token::Name("f").tag(6),
        Token::OpenParen.tag(7),
        Token::Name("x").tag(8),
        Token::CloseParen.tag(9),
        Token::Colon.tag(10),
        Token::Name("x").tag(12),
        Token::CloseBracket.tag(13),
    ]);

    assert_eq!(lex("[[]]"), vec![
        Token::OpenBracket.tag(0),
        Token::OpenBracket.tag(1),
        Token::CloseBracket.tag(2),
        Token::CloseBracket.tag(3),
    ]);
}
