use symbol_table::GlobalSymbol;

use crate::error::{Error, Span, Tagged};
use crate::wrappers::OrderedMap;


// Boxable
// ------------------------------------------------------------------------------------------------

/// Utility trait for converting any value to a boxed value.
pub trait Boxable<T> where T: Sized {
    /// Convert self to a boxed value.
    fn to_box(self) -> Box<T>;
}

impl<T> Boxable<T> for T {
    fn to_box(self) -> Box<T> { Box::new(self) }
}


// Taggable
// ------------------------------------------------------------------------------------------------

/// This trait provides the `tag` method, for wrapping a value in a [`Tagged`]
/// wrapper, which containts information about where in the source code this
/// object originated. This is used to report error messages.
///
/// There's no need to implement this trait beyond the blanket implementation.
pub trait Taggable: Sized {
    /// Wrap this object in a tagged wrapper.
    fn tag<T>(self, loc: T) -> Tagged<Self> where Span: From<T>;
}

impl<T> Taggable for T where T: Sized {
    fn tag<U>(self, loc: U) -> Tagged<Self> where Span: From<U> {
        Tagged::new(Span::from(loc), self)
    }
}


// Validatable
// ------------------------------------------------------------------------------------------------

/// This trait is implemented by all AST nodes that require a validation step,
/// to catch integrity errors which the parser either can't or won't catch.
pub trait Validatable {
    /// Validate this node and return a suitable error if necessary.
    ///
    /// By the Anna Karenina rule, there's no distinction on success.
    fn validate(&self) -> Result<(), Error>;
}

impl<T: Validatable> Validatable for Tagged<T> {
    fn validate(&self) -> Result<(), Error> {
        self.as_ref().validate()
    }
}


// ToVec
// ------------------------------------------------------------------------------------------------

/// Utility trait for converting things to vectors. This is used by the Object::list constructor.
pub trait ToVec<T> {
    fn to_vec(self) -> Vec<T>;
}

impl<T> ToVec<T> for () {
    fn to_vec(self) -> Vec<T> {
        vec![]
    }
}

impl<T> ToVec<T> for Vec<T> {
    fn to_vec(self) -> Vec<T> {
        self
    }
}


// ToMap
// ------------------------------------------------------------------------------------------------

/// Utility trait for converting things to maps. This is used by the Object::map constructor.
pub(crate) trait ToMap<K,V> {
    fn to_map(self) -> OrderedMap<K,V>;
}

impl<K,V> ToMap<K,V> for OrderedMap<K,V> {
    fn to_map(self) -> OrderedMap<K,V> {
        self
    }
}

impl<K,V> ToMap<K,V> for () {
    fn to_map(self) -> OrderedMap<K,V> {
        OrderedMap::new()
    }
}

impl<V,A,B> ToMap<GlobalSymbol,V> for Vec<(A,B)>
where
    A: AsRef<str>,
    V: From<B>,
{
    fn to_map(self) -> OrderedMap<GlobalSymbol,V> {
        let mut ret = OrderedMap::new();
        for (k, v) in self {
            ret.insert(GlobalSymbol::new(k.as_ref()), V::from(v));
        }
        ret
    }
}


// Peek
// ------------------------------------------------------------------------------------------------

/// Utility trait for unwrapping wrappers
pub(crate) trait Peek<T> {
    fn peek(&self) -> &T;
}
