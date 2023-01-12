use std::collections::HashSet;

use indexmap::IndexMap;
use symbol_table::GlobalSymbol;

use crate::error::{Error, Span, Tagged};
use crate::object::Key;


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


// Free
// ------------------------------------------------------------------------------------------------

/// Utility trait for traversing the AST to find free names.
///
/// A free name is a name in an expression that also isn't bound to a value in
/// that expression. Thus, when evaluating such an expression, free names must
/// be bound to values externally, prior to evaluation.
///
/// When evaluating (not calling) a function, free names must be captured from
/// the surrounding environment into a closure.
///
/// A well-formed top level expression has no free names except those imported.
///
/// Most nodes should implement [`FreeImpl`] instead of [`Free`], relying on the
/// default implementation of [`Free`].
pub trait Free {

    /// Return a set of all free names in this AST node.
    fn free(&self) -> HashSet<Key>;
}

/// Utility trait for implementing [`Free`] by mutating an existing set instead
/// of creating new ones at each AST node.
pub trait FreeImpl {

    /// Add all free names in this AST node to the set `free`.
    fn free_impl(&self, free: &mut HashSet<Key>);
}

/// Since almost all AST nodes occur only as tagged objects, provide a
/// pass-through implementation.
impl<T: FreeImpl> FreeImpl for Tagged<T> {
    fn free_impl(&self, free: &mut HashSet<Key>) {
        self.as_ref().free_impl(free)
    }
}

/// Default implementation of [`Free`] for anything that implements [`FreeImpl`].
impl<T: FreeImpl> Free for T {
    fn free(&self) -> HashSet<Key> {
        let mut free = HashSet::new();
        self.free_impl(&mut free);
        free
    }
}


// FreeAndBound
// ------------------------------------------------------------------------------------------------

/// Utility trait for traversing the AST to find free and bound names.
///
/// This is used for AST nodes that may both bind new names and refer to
/// existing names, such as binding patterns with default values. Such defaults
/// may rely on previously-bound names in the same pattern, thus necessitating
/// computing both free and bound names in the same traversal.
pub trait FreeAndBound {

    /// Add all free names in this AST node to the set `free`, and all bound
    /// names to the set `bound`.
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>);
}

/// Since almost all AST nodes occur only as tagged objects, provide a
/// pass-through implementation.
impl<T: FreeAndBound> FreeAndBound for Tagged<T> {
    fn free_and_bound(&self, free: &mut HashSet<Key>, bound: &mut HashSet<Key>) {
        self.as_ref().free_and_bound(free, bound)
    }
}


// HasSpan and HasMaybeSpan
// ------------------------------------------------------------------------------------------------

/// Implemented by all types that have a span (sourced by a range of text in a buffer.)
pub trait HasSpan {
    /// Return the span.
    fn span(&self) -> Span;
}

/// Implemented by all types that may habe a span (sourced by a range of text in a buffer.)
pub trait HasMaybeSpan {
    /// Return the span, if applicable.
    fn maybe_span(&self) -> Option<Span>;
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
    fn tag(self, loc: impl HasSpan) -> Tagged<Self>;
}

impl<T> Taggable for T where T: Sized {
    fn tag(self, loc: impl HasSpan) -> Tagged<Self> {
        Tagged::new(loc.span(), self)
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
pub trait ToMap<K,V> {
    fn to_map(self) -> IndexMap<K,V>;
}

impl<K,V> ToMap<K,V> for IndexMap<K,V> {
    fn to_map(self) -> IndexMap<K,V> {
        self
    }
}

impl<K,V> ToMap<K,V> for () {
    fn to_map(self) -> IndexMap<K,V> {
        IndexMap::new()
    }
}

impl<V,A,B> ToMap<GlobalSymbol,V> for Vec<(A,B)>
where
    A: AsRef<str>,
    V: From<B>,
{
    fn to_map(self) -> IndexMap<GlobalSymbol,V> {
        let mut ret = IndexMap::new();
        for (k, v) in self {
            ret.insert(GlobalSymbol::new(k.as_ref()), V::from(v));
        }
        ret
    }
}
