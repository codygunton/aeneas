//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Models of `alloc::collections` (BinaryHeap, VecDeque, BTreeMap, BTreeSet) and `alloc::rc`.
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

/// Ordered by `key` only: the payload tells equal elements apart.
pub struct Item {
    pub key: u32,
    pub payload: u32,
}

impl PartialEq for Item {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}
impl Eq for Item {}
impl PartialOrd for Item {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Item {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.key.cmp(&other.key)
    }
}

fn item(key: u32, payload: u32) -> Item {
    Item { key, payload }
}

#[verify::test]
pub fn test_binary_heap() {
    let mut h: BinaryHeap<Item> = BinaryHeap::default();
    assert!(h.is_empty());
    h.push(item(2, 0));
    h.push(item(5, 1));
    h.push(item(2, 2));
    h.push(item(5, 3));
    h.push(item(1, 4));
    h.push(item(2, 5));
    assert!(h.len() == 6);
    assert!(h.peek().unwrap().payload == 1);
    // Rust 1.96 pop order of the payloads: 1 3 2 0 5 4 (equal keys in heap order).
    assert!(h.pop().unwrap().payload == 1);
    assert!(h.pop().unwrap().payload == 3);
    assert!(h.pop().unwrap().payload == 2);
    assert!(h.pop().unwrap().payload == 0);
    assert!(h.pop().unwrap().payload == 5);
    assert!(h.pop().unwrap().payload == 4);
    assert!(h.pop().is_none());
    h.push(item(3, 6));
    h.clear();
    assert!(h.is_empty());
}

#[verify::test]
pub fn test_vec_deque() {
    let mut q: VecDeque<u32> = VecDeque::default();
    q.push_back(1);
    q.push_back(2);
    assert!(q.pop_front().unwrap() == 1);
    q.push_back(3);
    assert!(q.pop_front().unwrap() == 2);
    assert!(q.pop_front().unwrap() == 3);
    assert!(q.pop_front().is_none());
}

#[verify::test]
pub fn test_btree_map() {
    let mut m: BTreeMap<u32, u32> = BTreeMap::new();
    assert!(m.is_empty());
    assert!(m.insert(5, 50).is_none());
    assert!(m.insert(1, 10).is_none());
    assert!(m.insert(3, 30).is_none());
    assert!(m.insert(3, 31).unwrap() == 30);
    assert!(m.len() == 3);
    assert!(*m.get(&3).unwrap() == 31);
    assert!(m.get(&4).is_none());
    assert!(m.contains_key(&5));
    let mut it = m.iter();
    let (k0, _) = it.next().unwrap();
    assert!(*k0 == 1);
    let (k1, v1) = it.next().unwrap();
    assert!(*k1 == 3 && *v1 == 31);
    let mut r = m.range(2..6);
    assert!(*r.next().unwrap().0 == 3);
    assert!(*m.range(2..=5).last().unwrap().0 == 5);
    assert!(*m.range(..).max().unwrap().1 == 50);
    let mut vm = m.values_mut();
    if let Some(v) = vm.next() {
        *v += 1;
    }
    assert!(*m.get(&1).unwrap() == 11);
    *m.entry(7).or_default() += 70;
    *m.entry(1).or_default() += 100;
    assert!(*m.get(&7).unwrap() == 70);
    assert!(*m.get(&1).unwrap() == 111);
    // `retain` is not exercised: Aeneas cannot translate a closure taking `&mut V`.
    assert!(m.len() == 4);
    let c = m.clone();
    assert!(m.remove(&5).unwrap() == 50);
    assert!(m.remove(&5).is_none());
    assert!(c.len() == 4);
    m.clear();
    assert!(m.len() == 0);
    let d: BTreeMap<u32, u32> = BTreeMap::default();
    assert!(d.is_empty());
}

#[verify::test]
pub fn test_btree_set() {
    let mut xs: Vec<u32> = Vec::new();
    xs.push(5);
    xs.push(1);
    xs.push(3);
    xs.push(9);
    xs.push(3);
    let mut a: BTreeSet<u32> = BTreeSet::new();
    a.extend(xs);
    let mut ys: Vec<u32> = Vec::new();
    ys.push(3);
    ys.push(4);
    ys.push(9);
    let mut b: BTreeSet<u32> = BTreeSet::new();
    b.extend(ys);
    let mut d = a.difference(&b);
    assert!(d.size_hint().0 == 1);
    assert!(d.size_hint().1.unwrap() == 4);
    assert!(*d.next().unwrap() == 1);
    assert!(*d.next().unwrap() == 5);
    assert!(d.next().is_none());
    a.clear();
    let mut e = a.difference(&b);
    assert!(e.next().is_none());
}

#[verify::test]
pub fn test_rc() {
    let mut r: Rc<u32> = Rc::default();
    assert!(*r == 0);
    if let Some(x) = Rc::get_mut(&mut r) {
        *x = 4;
    }
    let r2 = r.clone();
    assert!(*r2 == 4);
    let _a: Arc<u32> = Arc::new(3);
}

#[cfg(test)]
mod tests {
    #[test]
    fn all() {
        super::test_binary_heap();
        super::test_vec_deque();
        super::test_btree_map();
        super::test_btree_set();
        super::test_rc();
    }
}
