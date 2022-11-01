#![feature(is_some_and)]

mod ast;
mod builtins;
mod eval;
mod object;
mod parsing;
mod traits;

#[cfg(test)]
mod tests;

pub use object::Object;
pub use parsing::parse;

pub fn eval(input: &str) -> Result<Object, String> {
    parsing::parse(input).and_then(|node| eval::eval(&node))
}
