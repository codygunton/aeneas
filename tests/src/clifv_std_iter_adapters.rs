//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
#![feature(register_tool)]
#![register_tool(verify)]
//! Models of the `core::iter` adapters and provided `Iterator` methods.
//! Stateful (`move`) closures check that closures are called lazily, in Rust's order.
//! Expected values: Rust 1.96 (`cargo test` in `tests/src`).

#[verify::test]
pub fn test_map_lazy() {
    let v: [u32; 4] = [1, 2, 3, 4];
    let mut calls: u32 = 0;
    let mut it = v.iter().map(move |x| {
        calls += 1;
        *x * 10 + calls
    });
    assert!(it.next() == Some(11));
    assert!(it.next() == Some(22));
    // `nth(1)` skips one element: the closure still runs for it.
    assert!(it.nth(1) == Some(44));
    assert!(it.next().is_none());
}

#[verify::test]
pub fn test_filter_count_fold() {
    let v: [u32; 6] = [1, 2, 3, 4, 5, 6];
    assert!(v.iter().filter(|x| **x % 2 == 0).count() == 3);
    let s = v.iter().filter(|x| **x > 2).fold(0u32, |a, x| a * 10 + *x);
    assert!(s == 3456);
    let mut it = v.iter().filter(|x| **x % 3 == 0);
    assert!(it.next() == Some(&3));
    assert!(it.next() == Some(&6));
    assert!(it.next().is_none());
}

#[verify::test]
pub fn test_filter_map_find_map() {
    let v: [u32; 5] = [7, 8, 9, 10, 11];
    let mut it = v.iter().filter_map(|x| if *x % 2 == 0 { Some(*x / 2) } else { None });
    assert!(it.next() == Some(4));
    assert!(it.next() == Some(5));
    assert!(it.next().is_none());
    let mut it2 = v.iter();
    let r = it2.find_map(|x| if *x > 8 { Some(*x + 100) } else { None });
    assert!(r == Some(109));
    // The search stopped right after `9`.
    assert!(it2.next() == Some(&10));
}

#[verify::test]
pub fn test_enumerate_fold_nth() {
    let v: [u32; 4] = [5, 6, 7, 8];
    let s = v.iter().enumerate().fold(0usize, |a, (i, x)| a + i * (*x as usize));
    assert!(s == 44);
    let mut it = v.iter().enumerate();
    let (i, x) = it.nth(2).unwrap();
    assert!(i == 2 && *x == 7);
    let (j, y) = it.next().unwrap();
    assert!(j == 3 && *y == 8);
    assert!(v.iter().enumerate().count() == 4);
}

#[verify::test]
pub fn test_chain() {
    let a: [u32; 2] = [1, 2];
    let b: [u32; 3] = [3, 4, 5];
    let mut it = a.iter().chain(b.iter());
    assert!(it.next() == Some(&1));
    assert!(it.nth(2) == Some(&4));
    assert!(it.next() == Some(&5));
    assert!(it.next().is_none());
    assert!(a.iter().chain(b.iter()).count() == 5);
    assert!(a.iter().chain(b.iter()).last() == Some(&5));
    assert!(a.iter().chain(b.iter()).fold(0u32, |s, x| s * 10 + *x) == 12345);
    let mut it2 = a.iter().chain(b.iter());
    assert!(it2.find(|x| **x > 3) == Some(&4));
    assert!(it2.next() == Some(&5));
    let (lo, hi) = a.iter().chain(b.iter()).size_hint();
    assert!(lo == 5 && hi == Some(5));
}

#[verify::test]
pub fn test_skip_take() {
    let v: [u32; 6] = [1, 2, 3, 4, 5, 6];
    let mut it = v.iter().skip(2);
    assert!(it.next() == Some(&3));
    assert!(it.nth(1) == Some(&5));
    assert!(v.iter().skip(4).count() == 2);
    assert!(v.iter().skip(10).count() == 0);
    assert!(v.iter().skip(1).last() == Some(&6));
    assert!(v.iter().skip(3).fold(0u32, |s, x| s + *x) == 15);
    let (lo, hi) = v.iter().skip(4).size_hint();
    assert!(lo == 2 && hi == Some(2));
    let mut t = v.iter().take(4);
    assert!(t.nth(1) == Some(&2));
    assert!(t.nth(5).is_none());
    assert!(t.next().is_none());
    assert!(v.iter().take(3).count() == 3);
    assert!(v.iter().take(3).fold(0u32, |s, x| s + *x) == 6);
    let (lo2, hi2) = v.iter().take(10).size_hint();
    assert!(lo2 == 6 && hi2 == Some(6));
}

#[verify::test]
pub fn test_skip_while_take_while() {
    let v: [u32; 6] = [1, 2, 5, 1, 7, 2];
    let mut it = v.iter().skip_while(|x| **x < 3);
    assert!(it.next() == Some(&5));
    // Once an element failed the predicate, everything is yielded.
    assert!(it.next() == Some(&1));
    let s = v.iter().take_while(|x| **x < 6).fold(0u32, |s, x| s + *x);
    assert!(s == 9);
}

#[verify::test]
pub fn test_peekable() {
    let v: [u32; 4] = [1, 2, 3, 4];
    let mut it = v.iter().peekable();
    assert!(it.peek() == Some(&&1));
    assert!(it.peek() == Some(&&1));
    assert!(it.next() == Some(&1));
    assert!(it.peek() == Some(&&2));
    assert!(it.nth(1) == Some(&3));
    let mut it2 = v.iter().peekable();
    it2.peek();
    assert!(it2.count() == 4);
    let mut it3 = v.iter().peekable();
    it3.peek();
    let (lo, hi) = it3.size_hint();
    assert!(lo == 4 && hi == Some(4));
    assert!(it3.last() == Some(&4));
}

#[verify::test]
pub fn test_rev() {
    let v: [u32; 4] = [1, 2, 3, 4];
    let mut it = v.iter().rev();
    assert!(it.next() == Some(&4));
    assert!(it.nth(1) == Some(&2));
    assert!(v.iter().rev().fold(0u32, |s, x| s * 10 + *x) == 4321);
    let mut it2 = v.iter().rev();
    assert!(it2.find(|x| **x < 3) == Some(&2));
    assert!(it2.next() == Some(&1));
}

#[verify::test]
pub fn test_zip() {
    let a: [u32; 3] = [1, 2, 3];
    let b: [u32; 2] = [10, 20];
    let s = a.iter().zip(b.iter()).fold(0u32, |s, (x, y)| s + *x * *y);
    assert!(s == 50);
    let mut it = a.iter().zip(b.iter());
    let (x, y) = it.nth(1).unwrap();
    assert!(*x == 2 && *y == 20);
    assert!(it.next().is_none());
    let (lo, hi) = a.iter().zip(b.iter()).size_hint();
    assert!(lo == 2 && hi == Some(2));
}

#[verify::test]
pub fn test_flat_map_flatten() {
    let v: [u32; 3] = [1, 2, 3];
    let s = v
        .iter()
        .flat_map(|x| core::iter::repeat(*x).take(*x as usize))
        .fold(0u32, |s, x| s * 10 + x);
    assert!(s == 122333);
    assert!(v.iter().flat_map(|x| 0..*x).count() == 6);
    assert!(v.iter().flat_map(|x| 0..*x).last() == Some(2));
    let mut it = v.iter().flat_map(|x| 0..*x);
    assert!(it.next() == Some(0));
    assert!(it.next() == Some(0));
    assert!(it.next_back() == Some(2));
    assert!(it.next_back() == Some(1));
    assert!(it.next() == Some(1));
    let o: [Option<u32>; 4] = [Some(1), None, Some(3), None];
    let mut f = o.into_iter().flatten();
    assert!(f.next() == Some(1));
    assert!(f.next() == Some(3));
    assert!(f.next().is_none());
    assert!(o.into_iter().flatten().count() == 2);
}

#[verify::test]
pub fn test_cloned_copied() {
    let v: [u32; 3] = [4, 5, 6];
    let mut c = v.iter().copied();
    assert!(c.next() == Some(4));
    assert!(c.nth(1) == Some(6));
    assert!(v.iter().copied().count() == 3);
    assert!(v.iter().copied().last() == Some(6));
    assert!(v.iter().cloned().fold(0u32, |s, x| s + x) == 15);
}

#[verify::test]
pub fn test_fuse_by_ref() {
    let v: [u32; 3] = [1, 2, 3];
    let mut it = v.iter().fuse();
    assert!(it.next() == Some(&1));
    let mut it2 = v.iter();
    let first_two = it2.by_ref().take(2).fold(0u32, |s, x| s + *x);
    assert!(first_two == 3);
    assert!(it2.next() == Some(&3));
}

#[verify::test]
pub fn test_provided_methods() {
    let v: [u32; 5] = [3, 9, 2, 9, 4];
    assert!(v.iter().max() == Some(&9));
    // `max_by` returns the last maximum.
    let m = v.iter().enumerate().max_by(|a, b| a.1.cmp(b.1)).unwrap();
    assert!(m.0 == 3);
    // `min_by_key` returns the first minimum.
    let w: [u32; 4] = [7, 4, 9, 4];
    let k = w.iter().enumerate().min_by_key(|p| *p.1).unwrap();
    assert!(k.0 == 1);
    assert!(v.iter().position(|x| *x == 9) == Some(1));
    assert!(v.iter().rposition(|x| *x == 9) == Some(3));
    assert!(v.iter().any(|x| *x == 2));
    assert!(!v.iter().all(|x| *x > 2));
    assert!(v.iter().copied().sum::<u32>() == 27);
    assert!(v.iter().map(|x| *x + 1).count() == 5);
    assert!(v.iter().map(|x| *x + 1).last() == Some(5));
    assert!(v.iter().map(|x| *x + 1).nth(1) == Some(10));
}

#[cfg(test)]
mod tests {
    #[test]
    fn all() {
        super::test_map_lazy();
        super::test_filter_count_fold();
        super::test_filter_map_find_map();
        super::test_enumerate_fold_nth();
        super::test_chain();
        super::test_skip_take();
        super::test_skip_while_take_while();
        super::test_peekable();
        super::test_rev();
        super::test_zip();
        super::test_flat_map_flatten();
        super::test_cloned_copied();
        super::test_fuse_by_ref();
        super::test_provided_methods();
    }
}
