#![feature(is_some_and)]

mod ast;
mod builtins;
mod eval;
mod parsing;
mod traits;
pub mod util;

pub mod object;

#[cfg(test)]
mod tests;

use std::fs::read_to_string;
use std::path::Path;

pub use object::Object;
pub use parsing::parse;


pub fn eval(input: &str, root: Option<&Path>) -> Result<Object, String> {
    if let Some(path) = root {
        parsing::parse(input).and_then(|file| eval::eval_path(&file, &path))
    } else {
        parsing::parse(input).and_then(|file| eval::eval_raw(&file))
    }
}


pub fn eval_raw(input: &str) -> Result<Object, String> {
    eval(input, None)
}


pub fn eval_file(input: &Path) -> Result<Object, String> {
    let contents = read_to_string(input).map_err(|x| x.to_string())?;
    eval(&contents, Some(input))
}
