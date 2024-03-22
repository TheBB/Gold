use crate::lexing::{Lexer, Token, TokenType};
use crate::traits::Taggable;

macro_rules! tok {
    ($x:expr, $tok:expr) => {{
        let res = $x;
        assert_eq!(res.as_ref().map(|r| &r.1), Ok(&$tok));
        res.unwrap().0
    }};
}

macro_rules! stop {
    ($x:ident) => {
        assert!($x.next_token().is_err())
    };
}

fn name(s: &'static str) -> Token {
    Token {
        kind: TokenType::Name,
        text: s,
    }
}
fn float(s: &'static str) -> Token {
    Token {
        kind: TokenType::Float,
        text: s,
    }
}
fn int(s: &'static str) -> Token {
    Token {
        kind: TokenType::Integer,
        text: s,
    }
}
fn stringlit(s: &'static str) -> Token {
    Token {
        kind: TokenType::StringLit,
        text: s,
    }
}
fn multistring(s: &'static str) -> Token {
    Token {
        kind: TokenType::MultiString,
        text: s,
    }
}
fn dquote() -> Token<'static> {
    Token {
        kind: TokenType::DoubleQuote,
        text: "\"",
    }
}
fn dollar() -> Token<'static> {
    Token {
        kind: TokenType::Dollar,
        text: "$",
    }
}
fn comma() -> Token<'static> {
    Token {
        kind: TokenType::Comma,
        text: ",",
    }
}
fn colon() -> Token<'static> {
    Token {
        kind: TokenType::Colon,
        text: ":",
    }
}
fn dcolon() -> Token<'static> {
    Token {
        kind: TokenType::DoubleColon,
        text: "::",
    }
}
fn ellipsis() -> Token<'static> {
    Token {
        kind: TokenType::Ellipsis,
        text: "...",
    }
}
fn openbrace() -> Token<'static> {
    Token {
        kind: TokenType::OpenBrace,
        text: "{",
    }
}
fn closebrace() -> Token<'static> {
    Token {
        kind: TokenType::CloseBrace,
        text: "}",
    }
}
fn openbracket() -> Token<'static> {
    Token {
        kind: TokenType::OpenBracket,
        text: "[",
    }
}
fn closebracket() -> Token<'static> {
    Token {
        kind: TokenType::CloseBracket,
        text: "]",
    }
}
fn openparen() -> Token<'static> {
    Token {
        kind: TokenType::OpenParen,
        text: "(",
    }
}
fn closeparen() -> Token<'static> {
    Token {
        kind: TokenType::CloseParen,
        text: ")",
    }
}

#[test]
fn whitespace() {
    let cache = Lexer::cache();

    let mut lex = Lexer::new("dingbob").with_cache(&cache);
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("\ndingbob").with_cache(&cache);
    lex = tok!(lex.next_token(), name("dingbob").tag(1..8).with_coord(1, 0));
    stop!(lex);

    let mut lex = Lexer::new("# this is a comment\ndingbob").with_cache(&cache);
    lex = tok!(
        lex.next_token(),
        name("dingbob").tag(20..27).with_coord(1, 0)
    );
    stop!(lex);

    let mut lex = Lexer::new("dingbob\n#this is a comment").with_cache(&cache);
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("dingbob#this is a comment").with_cache(&cache);
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("# this is a comment\n#a\n#b\ndingbob").with_cache(&cache);
    lex = tok!(
        lex.next_token(),
        name("dingbob").tag(26..33).with_coord(3, 0)
    );
    stop!(lex);
}

#[test]
fn booleans_and_null() {
    let cache = Lexer::cache();

    let mut lex = Lexer::new("true").with_cache(&cache);
    lex = tok!(lex.next_token(), name("true").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("false").with_cache(&cache);
    lex = tok!(lex.next_token(), name("false").tag(0..5));
    stop!(lex);

    let mut lex = Lexer::new("null").with_cache(&cache);
    lex = tok!(lex.next_token(), name("null").tag(0..4));
    stop!(lex);
}

#[test]
fn floats() {
    let cache = Lexer::cache();

    let mut lex = Lexer::new("0.0").with_cache(&cache);
    lex = tok!(lex.next_token(), float("0.0").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("0.").with_cache(&cache);
    lex = tok!(lex.next_token(), float("0.").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new(".0").with_cache(&cache);
    lex = tok!(lex.next_token(), float(".0").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new("0e0").with_cache(&cache);
    lex = tok!(lex.next_token(), float("0e0").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("0e1").with_cache(&cache);
    lex = tok!(lex.next_token(), float("0e1").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("1.").with_cache(&cache);
    lex = tok!(lex.next_token(), float("1.").tag(0..2));
    stop!(lex);

    let mut lex = Lexer::new("1e+1").with_cache(&cache);
    lex = tok!(lex.next_token(), float("1e+1").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("1e1").with_cache(&cache);
    lex = tok!(lex.next_token(), float("1e1").tag(0..3));
    stop!(lex);

    let mut lex = Lexer::new("1e-1").with_cache(&cache);
    lex = tok!(lex.next_token(), float("1e-1").tag(0..4));
    stop!(lex);
}

#[test]
fn strings() {
    let cache = Lexer::cache();

    let mut lex = Lexer::new("\"\"").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), dquote().tag(1));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob\"").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dquote().tag(8));
    stop!(lex);

    let mut lex = Lexer::new("\"ding\\\"bob\"").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("ding\\\"bob").tag(1..10));
    lex = tok!(lex.next_string(), dquote().tag(10));
    stop!(lex);

    let mut lex = Lexer::new("\"ding\\\\bob\"").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("ding\\\\bob").tag(1..10));
    lex = tok!(lex.next_string(), dquote().tag(10));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob$").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob$do").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    lex = tok!(lex.next_token(), name("do").tag(9..11));
    stop!(lex);

    let mut lex = Lexer::new("\"a + b = $a + $b\"").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("a + b = ").tag(1..9));
    lex = tok!(lex.next_string(), dollar().tag(9));
    lex = tok!(lex.next_token(), name("a").tag(10));
    lex = tok!(lex.next_string(), stringlit(" + ").tag(11..14));
    lex = tok!(lex.next_string(), dollar().tag(14));
    lex = tok!(lex.next_token(), name("b").tag(15));
    lex = tok!(lex.next_token(), dquote().tag(16));
    stop!(lex);

    let mut lex = Lexer::new("\"a + b = $a + $b = ${sum}\"").with_cache(&cache);
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

    let mut lex = Lexer::new("\"dingbob${a}\"").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    lex = tok!(lex.next_token(), openbrace().tag(9));
    lex = tok!(lex.next_token(), name("a").tag(10));
    lex = tok!(lex.next_token(), closebrace().tag(11));
    lex = tok!(lex.next_string(), dquote().tag(12));
    stop!(lex);

    let mut lex = Lexer::new("\"dingbob${ a}\"").with_cache(&cache);
    lex = tok!(lex.next_token(), dquote().tag(0));
    lex = tok!(lex.next_string(), stringlit("dingbob").tag(1..8));
    lex = tok!(lex.next_string(), dollar().tag(8));
    lex = tok!(lex.next_token(), openbrace().tag(9));
    lex = tok!(lex.next_token(), name("a").tag(11));
    lex = tok!(lex.next_token(), closebrace().tag(12));
    lex = tok!(lex.next_string(), dquote().tag(13));
    stop!(lex);

    let mut lex = Lexer::new("\"alpha\" \"bravo\"").with_cache(&cache);
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
    let cache = Lexer::cache();

    let mut lex = Lexer::new("dingbob").with_cache(&cache);
    lex = tok!(lex.next_token(), name("dingbob").tag(0..7));
    stop!(lex);

    let mut lex = Lexer::new("lets").with_cache(&cache);
    lex = tok!(lex.next_token(), name("lets").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("not1").with_cache(&cache);
    lex = tok!(lex.next_token(), name("not1").tag(0..4));
    stop!(lex);

    let mut lex = Lexer::new("null1").with_cache(&cache);
    lex = tok!(lex.next_token(), name("null1").tag(0..5));
    stop!(lex);
}

#[test]
fn lists() {
    let cache = Lexer::cache();

    let mut lex = Lexer::new("[]").with_cache(&cache);
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), closebracket().tag(1));
    stop!(lex);

    let mut lex = Lexer::new("[   ]").with_cache(&cache);
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), closebracket().tag(4));
    stop!(lex);

    let mut lex = Lexer::new("[true]").with_cache(&cache);
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), name("true").tag(1..5));
    lex = tok!(lex.next_token(), closebracket().tag(5));
    stop!(lex);

    let mut lex = Lexer::new("[\"\"]").with_cache(&cache);
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), dquote().tag(1));
    lex = tok!(lex.next_string(), dquote().tag(2));
    lex = tok!(lex.next_token(), closebracket().tag(3));
    stop!(lex);

    let mut lex = Lexer::new("[1,]").with_cache(&cache);
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), int("1").tag(1));
    lex = tok!(lex.next_token(), comma().tag(2));
    lex = tok!(lex.next_token(), closebracket().tag(3));
    stop!(lex);

    let mut lex = Lexer::new("[1, false, 2.3, \"fable\", lel]").with_cache(&cache);
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

    let mut lex = Lexer::new("[1, ...x, y]").with_cache(&cache);
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), int("1").tag(1));
    lex = tok!(lex.next_token(), comma().tag(2));
    lex = tok!(lex.next_token(), ellipsis().tag(4..7));
    lex = tok!(lex.next_token(), name("x").tag(7));
    lex = tok!(lex.next_token(), comma().tag(8));
    lex = tok!(lex.next_token(), name("y").tag(10));
    lex = tok!(lex.next_token(), closebracket().tag(11));
    stop!(lex);

    let mut lex = Lexer::new("[1, for x in y: x, 2]").with_cache(&cache);
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

    let mut lex = Lexer::new("[when f(x): x]").with_cache(&cache);
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

    let mut lex = Lexer::new("[[]]").with_cache(&cache);
    lex = tok!(lex.next_token(), openbracket().tag(0));
    lex = tok!(lex.next_token(), openbracket().tag(1));
    lex = tok!(lex.next_token(), closebracket().tag(2));
    lex = tok!(lex.next_token(), closebracket().tag(3));
    stop!(lex);
}

#[test]
fn maps() {
    let cache = Lexer::cache();

    let mut lex = Lexer::new("{}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), closebrace().tag(1));
    stop!(lex);

    let mut lex = Lexer::new("{  }").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), closebrace().tag(3));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("a").tag(1));
    lex = tok!(lex.next_token(), colon().tag(2));
    lex = tok!(lex.next_token(), int("1").tag(4));
    lex = tok!(lex.next_token(), closebrace().tag(5));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1,}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("a").tag(1));
    lex = tok!(lex.next_token(), colon().tag(2));
    lex = tok!(lex.next_token(), int("1").tag(4));
    lex = tok!(lex.next_token(), comma().tag(5));
    lex = tok!(lex.next_token(), closebrace().tag(6));
    stop!(lex);

    let mut lex = Lexer::new("{che9: false}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("che9").tag(1..5));
    lex = tok!(lex.next_token(), colon().tag(5));
    lex = tok!(lex.next_token(), name("false").tag(7..12));
    lex = tok!(lex.next_token(), closebrace().tag(12));
    stop!(lex);

    let mut lex = Lexer::new("{fable: \"fable\"}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("fable").tag(1..6));
    lex = tok!(lex.next_token(), colon().tag(6));
    lex = tok!(lex.next_token(), dquote().tag(8));
    lex = tok!(lex.next_string(), stringlit("fable").tag(9..14));
    lex = tok!(lex.next_string(), dquote().tag(14));
    lex = tok!(lex.next_token(), closebrace().tag(15));
    stop!(lex);

    let mut lex = Lexer::new("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}").with_cache(&cache);
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

    let mut lex = Lexer::new("{ident-with-hyphen: 1}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("ident-with-hyphen").tag(1..18));
    lex = tok!(lex.next_token(), colon().tag(18));
    lex = tok!(lex.next_token(), int("1").tag(20));
    lex = tok!(lex.next_token(), closebrace().tag(21));
    stop!(lex);

    let mut lex = Lexer::new("{$z: y}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), dollar().tag(1));
    lex = tok!(lex.next_token(), name("z").tag(2));
    lex = tok!(lex.next_token(), colon().tag(3));
    lex = tok!(lex.next_token(), name("y").tag(5));
    lex = tok!(lex.next_token(), closebrace().tag(6));
    stop!(lex);

    let mut lex = Lexer::new("{$\"z\": y}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), dollar().tag(1));
    lex = tok!(lex.next_token(), dquote().tag(2));
    lex = tok!(lex.next_string(), stringlit("z").tag(3));
    lex = tok!(lex.next_string(), dquote().tag(4));
    lex = tok!(lex.next_token(), colon().tag(5));
    lex = tok!(lex.next_token(), name("y").tag(7));
    lex = tok!(lex.next_token(), closebrace().tag(8));
    stop!(lex);

    let mut lex =
        Lexer::new(concat!("{\n", "   z:: here's some text\n", "}\n",)).with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).with_coord(1, 3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).with_coord(1, 4));
    lex = tok!(
        lex.next_multistring(3),
        multistring(" here's some text\n")
            .tag(8..26)
            .with_coord(1, 6)
    );
    lex = tok!(lex.next_token(), closebrace().tag(26).with_coord(2, 0));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z:: here's some\n",
        "       text\n",
        "}\n",
    ))
    .with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).with_coord(1, 3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).with_coord(1, 4));
    lex = tok!(
        lex.next_multistring(3),
        multistring(" here's some\n       text\n")
            .tag(8..33)
            .with_coord(1, 6)
    );
    lex = tok!(lex.next_token(), closebrace().tag(33).with_coord(3, 0));
    stop!(lex);

    let mut lex = Lexer::new(concat!("{\n", "   z:: here's some\n", "     text\n", "}\n",))
        .with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).with_coord(1, 3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).with_coord(1, 4));
    lex = tok!(
        lex.next_multistring(3),
        multistring(" here's some\n     text\n")
            .tag(8..31)
            .with_coord(1, 6)
    );
    lex = tok!(lex.next_token(), closebrace().tag(31).with_coord(3, 0));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "     here's some\n",
        "     text\n",
        "}\n",
    ))
    .with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).with_coord(1, 3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).with_coord(1, 4));
    lex = tok!(
        lex.next_multistring(3),
        multistring("\n     here's some\n     text\n")
            .tag(8..36)
            .with_coord(1, 6)
    );
    lex = tok!(lex.next_token(), closebrace().tag(36).with_coord(4, 0));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "     here's some\n",
        "       text\n",
        "}\n",
    ))
    .with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).with_coord(1, 3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).with_coord(1, 4));
    lex = tok!(
        lex.next_multistring(3),
        multistring("\n     here's some\n       text\n")
            .tag(8..38)
            .with_coord(1, 6)
    );
    lex = tok!(lex.next_token(), closebrace().tag(38).with_coord(4, 0));
    stop!(lex);

    let mut lex = Lexer::new(concat!(
        "{\n",
        "   z::\n",
        "       here's some\n",
        "     text\n",
        "}\n",
    ))
    .with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("z").tag(5).with_coord(1, 3));
    lex = tok!(lex.next_token(), dcolon().tag(6..8).with_coord(1, 4));
    lex = tok!(
        lex.next_multistring(3),
        multistring("\n       here's some\n     text\n")
            .tag(8..38)
            .with_coord(1, 6)
    );
    lex = tok!(lex.next_token(), closebrace().tag(38).with_coord(4, 0));
    stop!(lex);

    let mut lex =
        Lexer::new(concat!("{\n", "    a:: x\n", "    b: y,\n", "}\n",)).with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), name("a").tag(6).with_coord(1, 4));
    lex = tok!(lex.next_token(), dcolon().tag(7..9).with_coord(1, 5));
    lex = tok!(
        lex.next_multistring(4),
        multistring(" x\n").tag(9..12).with_coord(1, 7)
    );
    lex = tok!(lex.next_key(), name("b").tag(16).with_coord(2, 4));
    lex = tok!(lex.next_token(), colon().tag(17).with_coord(2, 5));
    lex = tok!(lex.next_token(), name("y").tag(19).with_coord(2, 7));
    lex = tok!(lex.next_token(), comma().tag(20).with_coord(2, 8));
    lex = tok!(lex.next_token(), closebrace().tag(22).with_coord(3, 0));
    stop!(lex);

    let mut lex = Lexer::new("{...y, x: 1}").with_cache(&cache);
    lex = tok!(lex.next_token(), openbrace().tag(0));
    lex = tok!(lex.next_key(), ellipsis().tag(1..4));
    lex = tok!(lex.next_token(), name("y").tag(4));
    lex = tok!(lex.next_token(), comma().tag(5));
    lex = tok!(lex.next_key(), name("x").tag(7));
    lex = tok!(lex.next_token(), colon().tag(8));
    lex = tok!(lex.next_token(), int("1").tag(10));
    lex = tok!(lex.next_token(), closebrace().tag(11));
    stop!(lex);

    let mut lex = Lexer::new("{for [x,y] in z: x: y}").with_cache(&cache);
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
