use std::collections::HashMap;

use crate::formatting::FormatSpec;
use crate::types::Key;
use crate::Object;

#[derive(Debug, Clone, Copy)]
pub enum BindingLoc {
    Enclosed(usize),
    Slot(usize)
}

pub trait Scope {
    fn new_constant(&mut self, value: Object) -> usize;
    fn new_fmt_spec(&mut self, spec: FormatSpec) -> usize;
    fn lookup_store(&mut self, name: Key) -> Option<usize>;
    fn lookup_load(&mut self, name: Key, require_cell: bool) -> Option<BindingLoc>;
    fn next_slot(&self) -> usize;
}

pub trait SubScope {
    fn announce_binding(&mut self, name: Key);
}

pub struct ClosureScope<'a> {
    parent: Option<&'a mut dyn Scope>,
    manager: LocalScopeManager,
    constants: Vec<Object>,
    fmt_specs: Vec<FormatSpec>,
    enclosed: HashMap<Key, usize>,
    requires: Vec<BindingLoc>,
}

impl<'a> ClosureScope<'a> {
    pub fn new(parent: Option<&'a mut dyn Scope>) -> Self {
        ClosureScope {
            parent,
            manager: LocalScopeManager::new(None),
            constants: Vec::new(),
            fmt_specs: Vec::new(),
            enclosed: HashMap::new(),
            requires: Vec::new(),
        }
    }

    pub fn finalize(self) -> (Vec<Object>, Vec<FormatSpec>, Vec<BindingLoc>, SlotCatalog) {
        let Self { manager, constants, fmt_specs, requires, .. } = self;
        (
            constants,
            fmt_specs,
            requires,
            manager.catalog(),
        )
    }
}

impl<'a> SubScope for ClosureScope<'a> {
    fn announce_binding(&mut self, name: Key) {
        self.manager.announce_binding(name);
    }
}

impl<'a> Scope for ClosureScope<'a> {
    fn new_constant(&mut self, value: Object) -> usize {
        self.constants.push(value);
        self.constants.len() - 1
    }

    fn new_fmt_spec(&mut self, spec: FormatSpec) -> usize {
        self.fmt_specs.push(spec);
        self.fmt_specs.len() - 1
    }

    fn lookup_store(&mut self, name: Key) -> Option<usize> {
        self.manager.lookup_store(name)
    }

    fn lookup_load(&mut self, name: Key, require_cell: bool) -> Option<BindingLoc> {
        let local = self.manager.lookup_load(name, require_cell);
        if local.is_some() {
            return local;
        }

        if let Some(loc) = self.enclosed.get(&name) {
            return Some(BindingLoc::Enclosed(*loc));
        }

        match self.parent.as_mut().map(|p| (*p).lookup_load(name, true)).flatten() {
            None => None,
            Some(parent_loc) => {
                self.requires.push(parent_loc);
                let local_index = self.enclosed.len();
                self.enclosed.insert(name, local_index);
                Some(BindingLoc::Enclosed(local_index))
            }
        }
    }

    fn next_slot(&self) -> usize {
        self.manager.next_slot
    }
}

#[derive(Debug, Copy, Clone)]
enum BindingStatus {
    Expected,
    ExpectedCell(usize),
    Local(usize),
    Cell(usize),
}

#[derive(Debug, Copy, Clone)]
pub enum SlotType {
    Local,
    Cell,
}

#[derive(Debug, Clone)]
pub struct SlotCatalog {
    map: HashMap<usize, SlotType>,
}

impl SlotCatalog {
    pub fn get(&self, index: &usize) -> Option<&SlotType> {
        self.map.get(index)
    }
}

struct LocalScopeManager {
    binding_status: HashMap<Key, BindingStatus>,
    next_slot: usize,
}

impl LocalScopeManager {
    fn new(parent: Option<&dyn Scope>) -> Self {
        Self {
            binding_status: HashMap::new(),
            next_slot: parent.map(|p| p.next_slot()).unwrap_or(0),
        }
    }

    fn announce_binding(&mut self, name: Key) {
        let current = self.binding_status.get(&name).copied();
        match current {
            None => { self.binding_status.insert(name, BindingStatus::Expected); }
            Some(BindingStatus::Expected) => { }
            _ => { panic!("announced future binding too late"); }
        }
    }

    fn lookup_store(&mut self, name: Key) -> Option<usize> {
        let current = self.binding_status.get(&name).copied();
        match current {
            None => None,
            Some(BindingStatus::Expected) => {
                self.next_slot += 1;
                self.binding_status.insert(name, BindingStatus::Local(self.next_slot - 1));
                Some(self.next_slot - 1)
            }
            Some(BindingStatus::ExpectedCell(index)) => {
                self.binding_status.insert(name, BindingStatus::Cell(index));
                Some(index)
            }
            Some(BindingStatus::Local(index)) => Some(index),
            Some(BindingStatus::Cell(index)) => Some(index),
        }
    }

    fn lookup_load(&mut self, name: Key, require_cell: bool) -> Option<BindingLoc> {
        let current = self.binding_status.get(&name).copied();
        match (current, require_cell) {
            (None, _) => None,
            (Some(BindingStatus::Expected), false) => None,
            (Some(BindingStatus::Expected), true) => {
                self.next_slot += 1;
                self.binding_status.insert(name, BindingStatus::ExpectedCell(self.next_slot - 1));
                Some(BindingLoc::Slot(self.next_slot - 1))
            }
            (Some(BindingStatus::ExpectedCell(_)), false) => None,
            (Some(BindingStatus::ExpectedCell(index)), true) => Some(BindingLoc::Slot(index)),
            (Some(BindingStatus::Local(index)), false) => Some(BindingLoc::Slot(index)),
            (Some(BindingStatus::Local(index)), true) => {
                self.binding_status.insert(name, BindingStatus::Cell(index));
                Some(BindingLoc::Slot(index))
            }
            (Some(BindingStatus::Cell(index)), _) => Some(BindingLoc::Slot(index)),
        }
    }

    fn catalog(self) -> SlotCatalog {
        let mut modes: HashMap<usize, SlotType> = HashMap::new();
        for (_, status) in self.binding_status {
            match status {
                BindingStatus::Cell(index) => { modes.insert(index, SlotType::Cell); },
                BindingStatus::Local(index) => { modes.insert(index, SlotType::Local); },
                _ => { panic!("expected binding but never used"); },
            }
        }
        SlotCatalog { map: modes }
    }
}

pub struct LocalScope<'a> {
    parent: &'a mut dyn Scope,
    manager: LocalScopeManager,
}

impl<'a> LocalScope<'a> {
    pub fn new(parent: &'a mut dyn Scope) -> Self {
        let manager = LocalScopeManager::new(Some(parent));
        Self { parent, manager }
    }

    pub fn catalog(self) -> SlotCatalog {
        self.manager.catalog()
    }
}

impl<'a> SubScope for LocalScope<'a> {
    fn announce_binding(&mut self, name: Key) {
        self.manager.announce_binding(name);
    }
}

impl<'a> Scope for LocalScope<'a> {
    fn new_constant(&mut self, value: Object) -> usize {
        self.parent.new_constant(value)
    }

    fn new_fmt_spec(&mut self, spec: FormatSpec) -> usize {
        self.parent.new_fmt_spec(spec)
    }

    fn lookup_store(&mut self, name: Key) -> Option<usize> {
        self.manager.lookup_store(name).or_else(|| self.parent.lookup_store(name))
    }

    fn lookup_load(&mut self, name: Key, require_cell: bool) -> Option<BindingLoc> {
        self.manager.lookup_load(name, require_cell).or_else(|| self.parent.lookup_load(name, require_cell))
    }

    fn next_slot(&self) -> usize {
        self.manager.next_slot
    }
}
