use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::hash::{BuildHasherDefault, Hasher};

use crate::interner::Symbol;

pub type SymHashMap<V> = HashMap<Symbol, V, BuildHasherDefault<IntHasher>>;
pub type SymHashSet = HashSet<Symbol, BuildHasherDefault<IntHasher>>;
pub type IntHashMap<V> = HashMap<usize, V, BuildHasherDefault<IntHasher>>;
pub type IntHashSet = HashSet<usize, BuildHasherDefault<IntHasher>>;

const K: u64 = 0x517cc1b727220a95;

/// A hasher for u32 and u64 only, e.g. symbols and type variable ids
#[derive(Default)]
pub struct IntHasher {
    hash: u64,
}

impl Hasher for IntHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        self.hash = match bytes.len() {
            4 => u32::from_ne_bytes(bytes[..4].try_into().unwrap()) as u64,
            8 => u64::from_ne_bytes(bytes[..8].try_into().unwrap()),
            _ => unreachable!(),
        };
    }

    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.hash = (i as u64).wrapping_mul(K);
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.hash = i.wrapping_mul(K);
    }

    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.hash = (i as u64).wrapping_mul(K);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.hash as u64
    }
}
