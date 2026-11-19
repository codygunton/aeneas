//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Models of `std::collections::{HashMap, HashSet}` and `std::hash::{RandomState, DefaultHasher}`.
// Iteration order of `RandomState` maps is randomized in Rust: the tests only observe
// order-independent results.
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, DefaultHasher, Hasher, RandomState};

#[verify::test]
pub fn test_hash_map() {
    let mut m: HashMap<u32, u32> = HashMap::new();
    assert!(m.is_empty());
    assert!(m.insert(1, 10).is_none());
    assert!(m.insert(2, 20).is_none());
    assert!(m.insert(1, 11).unwrap() == 10);
    assert!(m.len() == 2);
    assert!(*m.get(&1).unwrap() == 11);
    assert!(m.get(&3).is_none());
    assert!(m.contains_key(&2));
    assert!(m[&2] == 20);
    let v = m.entry(3).or_insert_with(|| 30);
    *v += 1;
    let v2 = m.entry(3).or_insert_with(|| 99);
    assert!(*v2 == 31);
    let mut total = 0;
    for (k, v) in &m {
        total += *k * *v;
    }
    assert!(total == 11 + 40 + 93);
    assert!(m.iter().count() == 3);
    assert!(m.iter().size_hint().0 == 3);
    let s = m.iter().fold(0u32, |acc, (_, v)| acc + *v);
    assert!(s == 11 + 20 + 31);
    let mut vs = 0;
    for v in m.values() {
        vs += *v;
    }
    assert!(vs == 62);
    assert!(m.remove(&2).unwrap() == 20);
    assert!(m.remove(&2).is_none());
    assert!(m.len() == 2);
    let w: HashMap<u32, u32> = HashMap::with_capacity(4);
    assert!(w.is_empty());
}

#[verify::test]
pub fn test_hash_set() {
    let mut s: HashSet<u32> = HashSet::default();
    assert!(s.insert(4));
    assert!(s.insert(5));
    assert!(!s.insert(4));
    assert!(s.contains(&5));
    assert!(!s.contains(&6));
    let mut n = 0;
    for x in &s {
        n += *x;
    }
    assert!(n == 9);
    let mut m = 0;
    for x in s {
        m += x;
    }
    assert!(m == 9);
}

#[verify::test]
pub fn test_default_hasher() {
    // Rust's DefaultHasher::new() is SipHash-1-3 with keys (0, 0); writes are streamed.
    let mut h = DefaultHasher::new();
    h.write(&[1, 2, 3]);
    h.write(&[4, 5, 6, 7, 8, 9, 10]);
    assert!(h.finish() == 0xcb7e0c6c167ecd44);
    let mut e = DefaultHasher::new();
    e.write(&[0, 0, 0, 0, 0, 0, 0, 0]);
    assert!(e.finish() == 0xbd60acb658c79e45);
    // RandomState keys are random in Rust: only compare hashers built from the same state.
    let s = RandomState::default();
    let mut h1 = s.build_hasher();
    h1.write(&[7, 7]);
    let mut h2 = s.build_hasher();
    h2.write(&[7]);
    h2.write(&[7]);
    assert!(h1.finish() == h2.finish());
}

#[cfg(test)]
mod tests {
    #[test]
    fn all() {
        super::test_hash_map();
        super::test_hash_set();
        super::test_default_hasher();
    }
}
