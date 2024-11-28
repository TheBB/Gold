//! String implementation.

use std::cmp::Ordering;
use std::fmt::Display;

use gc::{Finalize, Gc, Trace};
use serde::{Deserialize, Serialize};

use super::Key;

/// Convert a string to a displayable representation by adding escape sequences.
fn escape(s: &str) -> String {
    let mut r = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => {
                r.push_str("\\\"");
            }
            '\\' => {
                r.push_str("\\\\");
            }
            '$' => {
                r.push_str("\\$");
            }
            _ => {
                r.push(c);
            }
        }
    }
    r
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Debug, Trace, Finalize)]
enum StrV {
    Interned(#[unsafe_ignore_trace] Key),
    Natural(Gc<String>),
}

/// The string variant represents all possible Gold strings.
#[derive(Clone, Serialize, Deserialize, PartialEq, Debug, Trace, Finalize)]
pub struct Str(StrV);

impl PartialOrd<Str> for Str {
    fn partial_cmp(&self, other: &Str) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl From<&Str> for Key {
    fn from(value: &Str) -> Self {
        let Str(this) = value;
        match this {
            StrV::Interned(x) => *x,
            StrV::Natural(x) => Key::new(x.as_ref()),
        }
    }
}

impl From<Key> for Str {
    fn from(value: Key) -> Self {
        Str(StrV::Interned(value))
    }
}

impl Display for Str {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("\"{}\"", escape(self.as_str())))
    }
}

impl Str {
    /// Construct a new interned string.
    pub fn interned<T>(x: T) -> Self
    where
        Key: From<T>,
    {
        Self(StrV::Interned(Key::from(x)))
    }

    /// Construct a new natural (non-interned string).
    pub fn natural<T: AsRef<str>>(x: T) -> Self {
        Self(StrV::Natural(Gc::new(x.as_ref().to_string())))
    }

    /// Access the internal string slice.
    pub fn as_str(&self) -> &str {
        let Self(this) = self;
        match this {
            StrV::Interned(x) => x.as_str(),
            StrV::Natural(x) => x.as_str(),
        }
    }

    /// User (non-structural) equality does not differentiate between interned
    /// or non-interned strings.
    pub fn user_eq(&self, other: &Str) -> bool {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (StrV::Interned(x), StrV::Interned(y)) => x == y,
            _ => self.as_str() == other.as_str(),
        }
    }

    /// Concatenate two string variants (the + operator for strings).
    pub fn add(&self, other: &Str) -> Str {
        Self::natural(format!("{}{}", self.as_str(), other.as_str()))
    }
}

#[cfg(feature = "python")]
impl<'py> pyo3::IntoPyObject<'py> for Str {
    type Target = pyo3::types::PyString;
    type Output = pyo3::Bound<'py, Self::Target>;
    type Error = std::convert::Infallible;

    fn into_pyobject(self, py: pyo3::prelude::Python<'py>) -> Result<Self::Output, Self::Error> {
        self.as_str().into_pyobject(py)
    }
}

#[cfg(feature = "python")]
impl<'py, 'a> pyo3::IntoPyObject<'py> for &'a Str {
    type Target = pyo3::types::PyString;
    type Output = pyo3::Bound<'py, Self::Target>;
    type Error = std::convert::Infallible;

    fn into_pyobject(self, py: pyo3::prelude::Python<'py>) -> Result<Self::Output, Self::Error> {
        self.as_str().into_pyobject(py)
    }
}
