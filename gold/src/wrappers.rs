use std::hash::Hash;
use std::ops::Deref;

use gc::{Trace, Finalize, custom_trace, GcCell, GcCellRef, GcCellRefMut, BorrowMutError};
use indexmap::{IndexMap, map::Iter, map::IterMut};
use serde::{Serialize, Deserialize, Serializer, Deserializer};
use num_bigint::BigInt;

use crate::object::Map;


#[derive(Clone, Serialize, Deserialize, PartialEq, PartialOrd, Debug, Trace, Finalize)]
pub struct WBigInt(#[unsafe_ignore_trace] pub BigInt);

impl AsRef<BigInt> for WBigInt {
    fn as_ref(&self) -> &BigInt {
        &self.0
    }
}

impl Deref for WBigInt {
    type Target = BigInt;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}


#[derive(Clone, Debug)]
pub struct OrderedMap<K, V>(IndexMap<K, V>);

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

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.0.iter_mut()
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

impl<K, V: Finalize> Finalize for OrderedMap<K, V> {
    fn finalize(&self) {
        for (_, v) in self {
            v.finalize();
        }
    }
}

unsafe impl<K, V: Trace> Trace for OrderedMap<K, V> {
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


#[derive(Clone, Trace, Finalize, Debug, PartialEq)]
pub struct MapCell(GcCell<Map>);

impl MapCell {
    pub fn new(map: Map) -> MapCell {
        MapCell(GcCell::new(map))
    }

    pub fn borrow(&self) -> GcCellRef<'_, Map> {
        self.0.borrow()
    }

    pub fn borrow_mut(&self) -> GcCellRefMut<'_, Map> {
        self.0.borrow_mut()
    }

    pub fn try_borrow_mut(&self) -> Result<GcCellRefMut<'_, Map>, BorrowMutError> {
        self.0.try_borrow_mut()
    }
}

impl Serialize for MapCell {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.borrow().serialize(serializer)
    }
}

impl<'a> Deserialize<'a> for MapCell {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(MapCell(GcCell::new(Map::deserialize(deserializer)?)))
    }
}
