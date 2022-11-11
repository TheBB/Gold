use serde::{Serialize, Deserialize};


#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
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

impl From<()> for Location {
    fn from(_: ()) -> Self {
        Location { offset: 0, line: 0, length: 0 }
    }
}

impl<T> From<Tagged<T>> for Location {
    fn from(value: Tagged<T>) -> Self {
        value.location
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Tagged<T> {
    location: Location,
    contents: T,
}

impl<T> Tagged<T> {
    pub fn map<F, U>(self, f: F) -> Tagged<U> where F: FnOnce(T) -> U {
        Tagged::<U> {
            location: self.location,
            contents: f(self.contents),
        }
    }
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
