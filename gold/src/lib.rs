#![feature(is_some_and)]
#![feature(step_trait)]

#[macro_use]
extern crate lazy_static;

#[macro_use]
pub mod object;

mod ast;
mod builtins;
pub mod error;
pub mod eval;
mod lexing;
mod parsing;
mod traits;
mod util;

#[cfg(test)]
mod tests;

#[cfg(feature = "python")]
pub mod python;

use std::fs::read_to_string;
use std::path::Path;

use error::{Error, FileSystem};
use eval::{ImportResolver, NullResolver};
pub use object::Object;
pub use parsing::parse;


pub fn eval<T: ImportResolver>(input: &str, root: Option<&Path>, resolver: &T) -> Result<Object, Error> {
    let ret = if let Some(path) = root {
        parsing::parse(input).and_then(|file| eval::eval_path(&file, &path, resolver))
    } else {
        parsing::parse(input).and_then(|file| eval::eval_raw(&file, resolver))
    };

    ret.map_err(|err| err.render(input))
}


pub fn eval_raw(input: &str) -> Result<Object, Error> {
    eval(input, None, &NullResolver {})
}


pub fn eval_file(input: &Path) -> Result<Object, Error> {
    let contents = read_to_string(input).map_err(|_| Error::new(FileSystem::Read(input.to_owned())))?;
    eval(&contents, Some(input), &NullResolver {})
}
