use std::hash::Hash;

use gc::{custom_trace, Finalize, Trace};
use indexmap::{map::Iter, IndexMap};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[derive(Clone, Debug)]
pub(crate) struct OrderedMap<K, V>(pub(crate) IndexMap<K, V>);

impl<K, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        Self(IndexMap::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        self.0.iter()
    }
}

impl<K: Hash + Eq, V> OrderedMap<K, V> {
    pub fn get(&self, k: &K) -> Option<&V> {
        self.0.get(k)
    }

    pub fn remove(&mut self, k: &K) -> Option<V> {
        self.0.remove(k)
    }
}

impl<K: Hash + Eq, V2, V1: PartialEq<V2>> PartialEq<OrderedMap<K, V2>> for OrderedMap<K, V1> {
    fn eq(&self, other: &OrderedMap<K, V2>) -> bool {
        self.0.eq(&other.0)
    }
}

impl<K: Serialize + Hash + Eq, V: Serialize> Serialize for OrderedMap<K, V> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'a, K: Deserialize<'a> + Eq + Hash, V: Deserialize<'a>> Deserialize<'a> for OrderedMap<K, V> {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self(IndexMap::deserialize(deserializer)?))
    }
}

impl<K: Copy, V: Finalize> Finalize for OrderedMap<K, V> {
    fn finalize(&self) {
        for (_, v) in self {
            v.finalize();
        }
    }
}

unsafe impl<K: Copy, V: Trace> Trace for OrderedMap<K, V> {
    custom_trace!(this, {
        for (_, v) in this {
            mark(v);
        }
    });
}

impl<'a, K, V> IntoIterator for &'a OrderedMap<K, V> {
    type Item = <&'a IndexMap<K, V> as IntoIterator>::Item;
    type IntoIter = <&'a IndexMap<K, V> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

impl<K: Eq + Hash, V> OrderedMap<K, V> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.insert(key, value)
    }
}
