use serde::{Serialize, Deserialize};


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Location {
    pub offset: usize,
    pub line: u32,
    pub length: usize,
}

impl From<(usize, u32, usize)> for Location {
    fn from((offset, line, length): (usize, u32, usize)) -> Self {
        Location { offset, line, length }
    }
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Tagged<T> {
    location: Location,
    contents: T,
}

impl<T> AsRef<T> for Tagged<T> {
    fn as_ref(&self) -> &T {
        &self.contents
    }
}


pub trait Taggable: Sized {
    fn tag<T>(self, loc: T) -> Tagged<Self> where Location: From<T>;
}

impl<T> Taggable for T where T: Sized {
    fn tag<U>(self, loc: U) -> Tagged<Self> where Location: From<U> {
        Tagged::<Self> {
            location: Location::from(loc),
            contents: self
        }
    }
}
