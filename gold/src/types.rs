use std::fmt::Display;

use serde::{Serialize, Deserialize};
use symbol_table::GlobalSymbol;

use crate::{wrappers::OrderedMap, Object};


/// Type used for all interned strings, map keys, variable names, etc.
pub type Key = GlobalSymbol;


/// Type used for lists.
pub type List = Vec<Object>;


/// Type used for mapping of strings (that is, [`Key`]) to objects.
pub type Map = OrderedMap<Key, Object>;


/// Enumeration of all the different types a Gold object can have.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum Type {
    /// IntVariant
    Integer,

    /// f64
    Float,

    /// StrVariant
    String,

    /// bool
    Boolean,

    /// Vec<Object>
    List,

    /// IndexMap<Key, Object>
    Map,

    /// FuncVariant
    Function,

    /// Iterator
    Iterator,

    /// The empty variant
    Null,
}

// It's desirable that these names correspond to the built-in conversion
// functions. When Gold gets proper support for types, this source of ambiguity
// will be rectified.
impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer => f.write_str("int"),
            Self::Float => f.write_str("float"),
            Self::String => f.write_str("str"),
            Self::Boolean => f.write_str("bool"),
            Self::List => f.write_str("list"),
            Self::Map => f.write_str("map"),
            Self::Function => f.write_str("function"),
            Self::Iterator => f.write_str("iterator"),
            Self::Null => f.write_str("null"),
        }
    }
}
