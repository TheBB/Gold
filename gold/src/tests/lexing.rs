use crate::traits::Taggable;
use crate::lexing::{Lexer, Token, TokenType};


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


fn name(s: &'static str) -> Token { Token { kind: TokenType::Name, span: s } }
fn float(s: &'static str) -> Token { Token { kind: TokenType::Float, span: s } }
fn int(s: &'static str) -> Token { Token { kind: TokenType::Integer, span: s } }
fn stringlit(s: &'static str) -> Token { Token { kind: TokenType::StringLit, span: s } }
fn multistring(s: &'static str) -> Token { Token { kind: TokenType::MultiString, span: s } }
fn dquote() -> Token<'static> { Token { kind: TokenType::DoubleQuote, span: "\"" } }
fn dollar() -> Token<'static> { Token { kind: TokenType::Dollar, span: "$" } }
fn comma() -> Token<'static> { Token { kind: TokenType::Comma, span: "," } }
fn colon() -> Token<'static> { Token { kind: TokenType::Colon, span: ":" } }
fn dcolon() -> Token<'static> { Token { kind: TokenType::DoubleColon, span: "::" } }
fn ellipsis() -> Token<'static> { Token { kind: TokenType::Ellipsis, span: "..." } }
fn openbrace() -> Token<'static> { Token { kind: TokenType::OpenBrace, span: "{" } }
fn closebrace() -> Token<'static> { Token { kind: TokenType::CloseBrace, span: "}" } }
fn openbracket() -> Token<'static> { Token { kind: TokenType::OpenBracket, span: "[" } }
fn closebracket() -> Token<'static> { Token { kind: TokenType::CloseBracket, span: "]" } }
fn openparen() -> Token<'static> { Token { kind: TokenType::OpenParen, span: "(" } }
fn closeparen() -> Token<'static> { Token { kind: TokenType::CloseParen, span: ")" } }


#[test]
fn whitespace() {
    let mut lex = Lexer::new("dingbob");
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("\ndingbob");
    lex = tok!(lex.next_token(), name("dingbob").tag(1..8).line(2));
    stop!(lex);

    let mut lex = Lexer::new("# this is a comment\ndingbob");
    lex = tok!(lex.next_token(), name("dingbob").tag(20..27).line(2));
    stop!(lex);

    let mut lex = Lexer::new("dingbob\n#this is a comment");
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("dingbob#this is a comment");
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("# this is a comment\n#a\n#b\ndingbob");
    lex = tok!(lex.next_token(), name("dingbob").tag(26..33).line(4));
    stop!(lex);
}


#[test]
fn booleans_and_null() {
    let mut lex = Lexer::new("true");
    lex = tok!(lex.next_token(), name("true").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("false");
    lex = tok!(lex.next_token(), name("false").tag(0..5));
    stop!(lex);

    let mut lex = Lexer::new("null");
    lex = tok!(lex.next_token(), name("null").tag(0..4));
    stop!(lex);
}


#[test]
fn floats() {
    let mut lex = Lexer::new("0.0");
    lex = tok!(lex.next_token(), float("0.0").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("0.");
    lex = tok!(lex.next_token(), float("0.").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new(".0");
    lex = tok!(lex.next_token(), float(".0").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new("0e0");
    lex = tok!(lex.next_token(), float("0e0").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("0e1");
    lex = tok!(lex.next_token(), float("0e1").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("1.");
    lex = tok!(lex.next_token(), float("1.").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new("1e+1");
    lex = tok!(lex.next_token(), float("1e+1").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("1e1");
    lex = tok!(lex.next_token(), float("1e1").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("1e-1");
    lex = tok!(lex.next_token(), float("1e-1").tag(0..4));
    stop!(lex);
}


#[test]
fn strings() {
    let mut lex = Lexer::new("\"\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), dquote().tag(1));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dquote().tag(8));
    stop!(lex);

    let mut lex = Lexer::new("\"ding\\\"bob\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("ding\\\"bob").tag(1..10));
    lex = tok!(lex.next_string(), dquote().tag(10));
    stop!(lex);

    let mut lex = Lexer::new("\"ding\\\\bob\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("ding\\\\bob").tag(1..10));
    lex = tok!(lex.next_string(), dquote().tag(10));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob$");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob$do");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    lex = tok!(lex.next_token(), name("do").tag(9..11));
    stop!(lex);

    let mut lex = Lexer::new("\"a + b = $a + $b\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("a + b = ").tag(1..9));
    lex = tok!(lex.next_string(), dollar().tag(9));
    lex = tok!(lex.next_token(), name("a").tag(10));
    lex = tok!(lex.next_string(), stringlit(" + ").tag(11..14));
    lex = tok!(lex.next_string(), dollar().tag(14));
    lex = tok!(lex.next_token(), name("b").tag(15));
    lex = tok!(lex.next_token(), dquote().tag(16));
    stop!(lex);

    let mut lex = Lexer::new("\"a + b = $a + $b = ${sum}\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("a + b = ").tag(1..9));
    lex = tok!(lex.next_string(), dollar().tag(9));
    lex = tok!(lex.next_token(), name("a").tag(10));
    lex = tok!(lex.next_string(), stringlit(" + ").tag(11..14));
    lex = tok!(lex.next_string(), dollar().tag(14));
    lex = tok!(lex.next_token(), name("b").tag(15));
    lex = tok!(lex.next_string(), stringlit(" = ").tag(16..19));
    lex = tok!(lex.next_string(), dollar().tag(19));
    lex = tok!(lex.next_token(), openbrace().tag(20));
    lex = tok!(lex.next_token(), name("sum").tag(21..24));
    lex = tok!(lex.next_token(), closebrace().tag(24));
    lex = tok!(lex.next_string(), dquote().tag(25));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob${a}\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    lex = tok!(lex.next_token(), openbrace().tag(9));
    lex = tok!(lex.next_token(), name("a").tag(10));
    lex = tok!(lex.next_token(), closebrace().tag(11));
    lex = tok!(lex.next_string(), dquote().tag(12));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob${ a}\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    lex = tok!(lex.next_token(), openbrace().tag(9));
    lex = tok!(lex.next_token(), name("a").tag(11));
    lex = tok!(lex.next_token(), closebrace().tag(12));
    lex = tok!(lex.next_string(), dquote().tag(13));
    stop!(lex);

    let mut lex = Lexer::new("\"alpha\" \"bravo\"");
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("alpha").tag(1..6));
    lex = tok!(lex.next_string(), dquote().tag(6));
    lex = tok!(lex.next_token(), dquote().tag(8));
    lex = tok!(lex.next_string(), stringlit("bravo").tag(9..14));
    lex = tok!(lex.next_string(), dquote().tag(14));
    stop!(lex);
}


#[test]
fn identifiers() {
    let mut lex = Lexer::new("dingbob");
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("lets");
    lex = tok!(lex.next_token(), name("lets").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("not1");
    lex = tok!(lex.next_token(), name("not1").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("null1");
    lex = tok!(lex.next_token(), name("null1").tag(0..5));
    stop!(lex);
}


#[test]
fn lists() {
    let mut lex = Lexer::new("[]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), closebracket().tag(1));
    stop!(lex);

    let mut lex = Lexer::new("[   ]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), closebracket().tag(4));
    stop!(lex);

    let mut lex = Lexer::new("[true]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), name("true").tag(1..5));
    lex = tok!(lex.next_token(), closebracket().tag(5));
    stop!(lex);

    let mut lex = Lexer::new("[\"\"]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), dquote().tag(1));
    lex = tok!(lex.next_string(), dquote().tag(2));
    lex = tok!(lex.next_token(), closebracket().tag(3));
    stop!(lex);

    let mut lex = Lexer::new("[1,]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), int("1").tag(1));
    lex = tok!(lex.next_token(), comma().tag(2));
    lex = tok!(lex.next_token(), closebracket().tag(3));
    stop!(lex);

    let mut lex = Lexer::new("[1, false, 2.3, \"fable\", lel]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), int("1").tag(1));
    lex = tok!(lex.next_token(), comma().tag(2));
    lex = tok!(lex.next_token(), name("false").tag(4..9));
    lex = tok!(lex.next_token(), comma().tag(9));
    lex = tok!(lex.next_token(), float("2.3").tag(11..14));
    lex = tok!(lex.next_token(), comma().tag(14));
    lex = tok!(lex.next_token(), dquote().tag(16));
    lex = tok!(lex.next_string(), stringlit("fable").tag(17..22));
    lex = tok!(lex.next_string(), dquote().tag(22));
    lex = tok!(lex.next_token(), comma().tag(23));
    lex = tok!(lex.next_token(), name("lel").tag(25..28));
    lex = tok!(lex.next_token(), closebracket().tag(28));
    stop!(lex);

    let mut lex = Lexer::new("[1, ...x, y]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), int("1").tag(1));
    lex = tok!(lex.next_token(), comma().tag(2));
    lex = tok!(lex.next_token(), ellipsis().tag(4..7));
    lex = tok!(lex.next_token(), name("x").tag(7));
    lex = tok!(lex.next_token(), comma().tag(8));
    lex = tok!(lex.next_token(), name("y").tag(10));
    lex = tok!(lex.next_token(), closebracket().tag(11));
    stop!(lex);

    let mut lex = Lexer::new("[1, for x in y: x, 2]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), int("1").tag(1));
    lex = tok!(lex.next_token(), comma().tag(2));
    lex = tok!(lex.next_token(), name("for").tag(4..7));
    lex = tok!(lex.next_token(), name("x").tag(8));
    lex = tok!(lex.next_token(), name("in").tag(10..12));
    lex = tok!(lex.next_token(), name("y").tag(13));
    lex = tok!(lex.next_token(), colon().tag(14));
    lex = tok!(lex.next_token(), name("x").tag(16));
    lex = tok!(lex.next_token(), comma().tag(17));
    lex = tok!(lex.next_token(), int("2").tag(19));
    lex = tok!(lex.next_token(), closebracket().tag(20));
    stop!(lex);

    let mut lex = Lexer::new("[when f(x): x]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), name("when").tag(1..5));
    lex = tok!(lex.next_token(), name("f").tag(6));
    lex = tok!(lex.next_token(), openparen().tag(7));
    lex = tok!(lex.next_token(), name("x").tag(8));
    lex = tok!(lex.next_token(), closeparen().tag(9));
    lex = tok!(lex.next_token(), colon().tag(10));
    lex = tok!(lex.next_token(), name("x").tag(12));
    lex = tok!(lex.next_token(), closebracket().tag(13));
    stop!(lex);

    let mut lex = Lexer::new("[[]]");
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), openbracket().tag(1));
    lex = tok!(lex.next_token(), closebracket().tag(2));
    lex = tok!(lex.next_token(), closebracket().tag(3));
    stop!(lex);
}


#[test]
fn maps() {
    let mut lex = Lexer::new("{}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), closebrace().tag(1));
    stop!(lex);

    let mut lex = Lexer::new("{  }");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), closebrace().tag(3));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("a").tag(1));
    lex = tok!(lex.next_token(), colon().tag(2));
    lex = tok!(lex.next_token(), int("1").tag(4));
    lex = tok!(lex.next_token(), closebrace().tag(5));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1,}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("a").tag(1));
    lex = tok!(lex.next_token(), colon().tag(2));
    lex = tok!(lex.next_token(), int("1").tag(4));
    lex = tok!(lex.next_token(), comma().tag(5));
    lex = tok!(lex.next_token(), closebrace().tag(6));
    stop!(lex);

    let mut lex = Lexer::new("{che9: false}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("che9").tag(1..5));
    lex = tok!(lex.next_token(), colon().tag(5));
    lex = tok!(lex.next_token(), name("false").tag(7..12));
    lex = tok!(lex.next_token(), closebrace().tag(12));
    stop!(lex);

    let mut lex = Lexer::new("{fable: \"fable\"}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("fable").tag(1..6));
    lex = tok!(lex.next_token(), colon().tag(6));
    lex = tok!(lex.next_token(), dquote().tag(8));
    lex = tok!(lex.next_string(), stringlit("fable").tag(9..14));
    lex = tok!(lex.next_string(), dquote().tag(14));
    lex = tok!(lex.next_token(), closebrace().tag(15));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("a").tag(1));
    lex = tok!(lex.next_token(), colon().tag(2));
    lex = tok!(lex.next_token(), int("1").tag(4));
    lex = tok!(lex.next_token(), comma().tag(5));
    lex = tok!(lex.next_key(), name("b").tag(7));
    lex = tok!(lex.next_token(), colon().tag(8));
    lex = tok!(lex.next_token(), name("true").tag(10..14));
    lex = tok!(lex.next_token(), comma().tag(14));
    lex = tok!(lex.next_key(), name("c").tag(16));
    lex = tok!(lex.next_token(), colon().tag(17));
    lex = tok!(lex.next_token(), float("2.e1").tag(19..23));
    lex = tok!(lex.next_token(), comma().tag(23));
    lex = tok!(lex.next_key(), name("d").tag(25));
    lex = tok!(lex.next_token(), colon().tag(26));
    lex = tok!(lex.next_token(), dquote().tag(28));
    lex = tok!(lex.next_string(), stringlit("hoho").tag(29..33));
    lex = tok!(lex.next_string(), dquote().tag(33));
    lex = tok!(lex.next_token(), comma().tag(34));
    lex = tok!(lex.next_key(), name("e").tag(36));
    lex = tok!(lex.next_token(), colon().tag(37));
    lex = tok!(lex.next_token(), float("1e1").tag(39..42));
    lex = tok!(lex.next_token(), closebrace().tag(42));
    stop!(lex);

    let mut lex = Lexer::new("{ident-with-hyphen: 1}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("ident-with-hyphen").tag(1..18));
    lex = tok!(lex.next_token(), colon().tag(18));
    lex = tok!(lex.next_token(), int("1").tag(20));
    lex = tok!(lex.next_token(), closebrace().tag(21));
    stop!(lex);

    let mut lex = Lexer::new("{$z: y}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), dollar().tag(1));
    lex = tok!(lex.next_token(), name("z").tag(2));
    lex = tok!(lex.next_token(), colon().tag(3));
    lex = tok!(lex.next_token(), name("y").tag(5));
    lex = tok!(lex.next_token(), closebrace().tag(6));
    stop!(lex);

    let mut lex = Lexer::new("{$\"z\": y}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), dollar().tag(1));
    lex = tok!(lex.next_token(), dquote().tag(2));
    lex = tok!(lex.next_string(), stringlit("z").tag(3));
    lex = tok!(lex.next_string(), dquote().tag(4));
    lex = tok!(lex.next_token(), colon().tag(5));
    lex = tok!(lex.next_token(), name("y").tag(7));
    lex = tok!(lex.next_token(), closebrace().tag(8));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z:: here's some text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).line(2).col(3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).line(2).col(4));
    lex = tok!(lex.next_multistring(3), multistring(" here's some text\n").tag(8..26).line(2).col(6));
    lex = tok!(lex.next_token(), closebrace().tag(26).line(3));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z:: here's some\n",
        "       text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).line(2).col(3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).line(2).col(4));
    lex = tok!(lex.next_multistring(3), multistring(" here's some\n       text\n").tag(8..33).line(2).col(6));
    lex = tok!(lex.next_token(), closebrace().tag(33).line(4));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z:: here's some\n",
        "     text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).line(2).col(3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).line(2).col(4));
    lex = tok!(lex.next_multistring(3), multistring(" here's some\n     text\n").tag(8..31).line(2).col(6));
    lex = tok!(lex.next_token(), closebrace().tag(31).line(4));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "     here's some\n",
        "     text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).line(2).col(3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).line(2).col(4));
    lex = tok!(lex.next_multistring(3), multistring("\n     here's some\n     text\n").tag(8..36).line(2).col(6));
    lex = tok!(lex.next_token(), closebrace().tag(36).line(5));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "     here's some\n",
        "       text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).line(2).col(3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).line(2).col(4));
    lex = tok!(lex.next_multistring(3), multistring("\n     here's some\n       text\n").tag(8..38).line(2).col(6));
    lex = tok!(lex.next_token(), closebrace().tag(38).line(5));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "       here's some\n",
        "     text\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).line(2).col(3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).line(2).col(4));
    lex = tok!(lex.next_multistring(3), multistring("\n       here's some\n     text\n").tag(8..38).line(2).col(6));
    lex = tok!(lex.next_token(), closebrace().tag(38).line(5));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "    a:: x\n",
        "    b: y,\n",
        "}\n",
    ));
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("a").tag(6).line(2).col(4));
    lex = tok!(lex.next_token(), dcolon().tag(7..9).line(2).col(5));
    lex = tok!(lex.next_multistring(4), multistring(" x\n").tag(9..12).line(2).col(7));
    lex = tok!(lex.next_key(), name("b").tag(16).line(3).col(4));
    lex = tok!(lex.next_token(), colon().tag(17).line(3).col(5));
    lex = tok!(lex.next_token(), name("y").tag(19).line(3).col(7));
    lex = tok!(lex.next_token(), comma().tag(20).line(3).col(8));
    lex = tok!(lex.next_token(), closebrace().tag(22).line(4));
    stop!(lex);

    let mut lex = Lexer::new("{...y, x: 1}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), ellipsis().tag(1..4));
    lex = tok!(lex.next_token(), name("y").tag(4));
    lex = tok!(lex.next_token(), comma().tag(5));
    lex = tok!(lex.next_key(), name("x").tag(7));
    lex = tok!(lex.next_token(), colon().tag(8));
    lex = tok!(lex.next_token(), int("1").tag(10));
    lex = tok!(lex.next_token(), closebrace().tag(11));
    stop!(lex);

    let mut lex = Lexer::new("{for [x,y] in z: x: y}");
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("for").tag(1..4));
    lex = tok!(lex.next_token(), openbracket().tag(5));
    lex = tok!(lex.next_token(), name("x").tag(6));
    lex = tok!(lex.next_token(), comma().tag(7));
    lex = tok!(lex.next_token(), name("y").tag(8));
    lex = tok!(lex.next_token(), closebracket().tag(9));
    lex = tok!(lex.next_token(), name("in").tag(11..13));
    lex = tok!(lex.next_token(), name("z").tag(14));
    lex = tok!(lex.next_token(), colon().tag(15));
    lex = tok!(lex.next_key(), name("x").tag(17));
    lex = tok!(lex.next_token(), colon().tag(18));
    lex = tok!(lex.next_token(), name("y").tag(20));
    lex = tok!(lex.next_token(), closebrace().tag(21));
    stop!(lex);
}
