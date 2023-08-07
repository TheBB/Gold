use std::collections::HashSet;

use symbol_table::GlobalSymbol;

use crate::error::{Error, Span, Tagged, Syntax, Action};
use crate::object::Key;
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



// Free and bound name traversal traits
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
pub trait FreeNames {
    /// Traverse the AST tree and call [`NameReceiver::free`] for every free
    /// name.
    fn traverse_free(&self, receiver: &mut impl NameReceiver);

    /// Return a HashSet containing all the free names.
    fn free(&self) -> HashSet<Key> {
        let mut receiver = FreeNameCollector::new();
        self.traverse_free(&mut receiver);
        receiver.finish()
    }
}

/// Since almost all AST nodes occur only as tagged objects, provide a
/// pass-through implementation.
impl<T: FreeNames> FreeNames for Tagged<T> {
    fn traverse_free(&self, new_free: &mut impl NameReceiver) {
        self.as_ref().traverse_free(new_free)
    }
}


/// Utility trait for traversing the AST to find free and bound names.
///
/// This is used for AST nodes that may both bind new names and refer to
/// existing names, such as binding patterns with default values. Such defaults
/// may rely on previously-bound names in the same pattern, thus necessitating
/// computing both free and bound names in the same traversal.
pub trait FreeAndBoundNames {
    /// Traverse the AST tree and call [`NameReceiver::free`] for all free
    /// names, and [`NameReceiver::bound`] for all bound names.
    fn traverse_free_bound(&self, receiver: &mut impl NameReceiver);
}

/// Since almost all AST nodes occur only as tagged objects, provide a
/// pass-through implementation.
impl<T: FreeAndBoundNames> FreeAndBoundNames for Tagged<T> {
    fn traverse_free_bound(&self, receiver: &mut impl NameReceiver) {
        self.as_ref().traverse_free_bound(receiver);
    }
}


/// Callback trait for traversing the AST for free and bound names.
pub trait NameReceiver {
    /// Called when a new free name is found.
    fn free(&mut self, name: &Tagged<Key>);

    /// Called when a new bound name is found.
    fn bound(&mut self, name: &Tagged<Key>);
}


/// Implementation of [`NameReceiver`] for collecting free names.
pub struct FreeNameCollector(HashSet<Key>);

impl FreeNameCollector {
    fn new() -> Self {
        Self(HashSet::new())
    }

    fn finish(self) -> HashSet<Key> {
        self.0
    }
}

impl NameReceiver for FreeNameCollector {
    fn free(&mut self, name: &Tagged<Key>) {
        self.0.insert(**name);
    }

    fn bound(&mut self, _: &Tagged<Key>) { }
}


/// Implementation of [`NameReceiver`] for introducing additional bindings,
/// passing through only unknown free names to the underlying [`NameReceiver`].
pub struct NameBinder<'a>(&'a mut dyn NameReceiver, HashSet<Key>);

impl<'a> NameBinder<'a> {
    pub fn new(receiver: &'a mut dyn NameReceiver) -> Self {
        Self(receiver, HashSet::new())
    }
}

impl<'a> NameReceiver for NameBinder<'a> {
    fn free(&mut self, name: &Tagged<Key>) {
        let Self(receiver, bound) = self;
        if !bound.contains(&**name) {
            (*receiver).free(name);
        }
    }

    fn bound(&mut self, name: &Tagged<Key>) {
        let Self(_, bound) = self;
        bound.insert(**name);
    }
}



/// Implementation of [`NameReceiver`] for collecting bound names, creating
/// an error in case of duplicates.
pub struct BoundNameCollector(HashSet<Key>, Option<Error>);

impl BoundNameCollector {
    pub fn new() -> Self {
        Self(HashSet::new(), None)
    }

    pub fn finish(self) -> Result<(), Error> {
        if let Some(err) = self.1 {
            Err(err)
        } else {
            Ok(())
        }
    }
}

impl NameReceiver for BoundNameCollector {
    fn free(&mut self, _: &Tagged<Key>) { }

    fn bound(&mut self, name: &Tagged<Key>) {
        let Self(bound, error) = self;
        if error.is_some() {
            return;
        }
        if bound.contains(&**name) {
            *error = Some(Error::new(Syntax::DuplicateBindings(**name)).tag(name, Action::Parse))
        }
        self.0.insert(**name);
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
