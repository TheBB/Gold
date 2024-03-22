//! String implementation.

use std::cmp::Ordering;
use std::fmt::Display;

use gc::{Finalize, Gc, Trace};
use serde::{Serialize, Deserialize};

use super::Key;


/// Convert a string to a displayable representation by adding escape sequences.
fn escape(s: &str) -> String {
    let mut r = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => { r.push_str("\\\""); }
            '\\' => { r.push_str("\\\\"); }
            '$' => { r.push_str("\\$"); }
            _ => { r.push(c); }
        }
    }
    r
}


/// The string variant represents all possible Gold strings.
#[derive(Clone, Serialize, Deserialize, PartialEq, Debug, Trace, Finalize)]
pub enum StrVariant {
    /// Interned string. All strings that fall in the following categories are interned:
    /// - identifiers
    /// - map keys
    /// - strings no more than 20 characters long
    ///
    /// Note that Gold does not garbage-collect interned strings.
    Interned(#[unsafe_ignore_trace] Key),

    /// Natural (non-interned) string. If a string is not interned, or if it
    /// requires runtime evaluation (e.g. it is interpolated, or is the result
    /// of concatenation), then it is not interned.
    Natural(Gc<String>),
}

impl PartialOrd<StrVariant> for StrVariant {
    fn partial_cmp(&self, other: &StrVariant) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl From<&StrVariant> for Key {
    fn from(value: &StrVariant) -> Self {
        match value {
            StrVariant::Interned(x) => *x,
            StrVariant::Natural(x) => Key::new(x.as_ref()),
        }
    }
}

impl Display for StrVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("\"{}\"", escape(self.as_str())))
    }
}

impl StrVariant {
    /// Construct a new interned string.
    pub fn interned<T: AsRef<str>>(x: T) -> Self {
        Self::Interned(Key::new(x))
    }

    /// Construct a new natural (non-interned string).
    pub fn natural<T: AsRef<str>>(x: T) -> Self {
        Self::Natural(Gc::new(x.as_ref().to_string()))
    }

    /// Access the internal string slice.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Interned(x) => x.as_str(),
            Self::Natural(x) => x.as_str(),
        }
    }

    /// User (non-structural) equality does not differentiate between interned
    /// or non-interned strings.
    pub fn user_eq(&self, other: &StrVariant) -> bool {
        match (self, other) {
            (Self::Interned(x), Self::Interned(y)) => x == y,
            _ => self.as_str() == other.as_str(),
        }
    }

    /// Concatenate two string variants (the + operator for strings).
    pub fn add(&self, other: &StrVariant) -> StrVariant {
        Self::natural(format!("{}{}", self.as_str(), other.as_str()))
    }
}

