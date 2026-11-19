//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
#![feature(register_tool)]
#![register_tool(verify)]
//! Models of `core::slice` methods and slice iterators.
//! Expected values: Rust 1.96 (`cargo test` in `tests/src`).


fn res<T, E>(r: Result<T, E>) -> (bool, Option<T>, Option<E>) {
    match r {
        Ok(x) => (true, Some(x), None),
        Err(e) => (false, None, Some(e)),
    }
}

#[verify::test]
pub fn test_first_last() {
    let v: [u32; 3] = [1, 2, 3];
    let s = &v[..];
    assert!(s.first() == Some(&1));
    assert!(s.last() == Some(&3));
    let e: [u32; 0] = [];
    assert!(e[..].first().is_none());
    let (x, rest) = s.split_first().unwrap();
    assert!(*x == 1 && rest.len() == 2);
}

#[verify::test]
pub fn test_windows() {
    let v: [u32; 4] = [1, 2, 3, 4];
    let s = v.windows(2).fold(0u32, |a, w| a * 10 + w[0] + w[1]);
    assert!(s == 357);
    assert!(v.windows(3).count() == 2);
    assert!(v.windows(5).count() == 0);
    let l = v.windows(3).last().unwrap();
    assert!(l[0] == 2 && l[2] == 4);
    let mut it = v.windows(2);
    let n = it.nth(1).unwrap();
    assert!(n[0] == 2 && n[1] == 3);
    let m = it.next().unwrap();
    assert!(m[0] == 3);
    assert!(it.next().is_none());
}

#[verify::test]
pub fn test_array_windows() {
    let v: [u32; 4] = [1, 2, 3, 4];
    let s = v.array_windows::<2>().fold(0u32, |a, [x, y]| a * 10 + *x * *y);
    assert!(s == 2*100 + 6*10 + 12);
    assert!(v.array_windows::<3>().count() == 2);
    let l = v.array_windows::<2>().last().unwrap();
    assert!(l[0] == 3 && l[1] == 4);
    let mut it = v.array_windows::<2>();
    let n = it.nth(2).unwrap();
    assert!(n[0] == 3);
    assert!(it.next().is_none());
}

#[verify::test]
pub fn test_chunks_exact() {
    let v: [u32; 7] = [1, 2, 3, 4, 5, 6, 7];
    assert!(v.chunks_exact(2).count() == 3);
    let l = v.chunks_exact(2).last().unwrap();
    assert!(l[0] == 5);
    let mut it = v.chunks_exact(2);
    let b = it.next_back().unwrap();
    assert!(b[1] == 6);
    let n = it.nth(1).unwrap();
    assert!(n[0] == 3);
    assert!(it.next().is_none());
    let (lo, hi) = v.chunks_exact(3).size_hint();
    assert!(lo == 2 && hi == Some(2));
}

#[verify::test]
pub fn test_binary_search() {
    let v: [u32; 7] = [1, 3, 3, 3, 5, 8, 13];
    // Rust's branch-free search returns this particular index among the equal elements.
    assert!(res(v.binary_search_by(|x| x.cmp(&3))).1 == Some(3));
    assert!(res(v.binary_search_by(|x| x.cmp(&4))).2 == Some(4));
    assert!(res(v.binary_search_by(|x| x.cmp(&0))).2 == Some(0));
    assert!(res(v.binary_search_by(|x| x.cmp(&20))).2 == Some(7));
    let p: [(u32, u32); 4] = [(1, 10), (2, 20), (4, 40), (8, 80)];
    assert!(res(p.binary_search_by_key(&4, |e| e.0)).1 == Some(2));
    assert!(res(p.binary_search_by_key(&5, |e| e.0)).2 == Some(3));
    assert!(v.partition_point(|x| *x < 5) == 4);
    let e: [u32; 0] = [];
    assert!(res(e.binary_search_by(|x| x.cmp(&1))).2 == Some(0));
}

#[verify::test]
pub fn test_sort_unstable() {
    let mut v: [u32; 6] = [5, 1, 4, 1, 3, 2];
    v.sort_unstable();
    assert!(v[0] == 1 && v[1] == 1 && v[2] == 2 && v[3] == 3 && v[4] == 4 && v[5] == 5);
    let mut p: [(u32, u32); 4] = [(3, 1), (1, 2), (2, 3), (0, 4)];
    p.sort_unstable_by_key(|e| e.0);
    assert!(p[0].1 == 4 && p[1].1 == 2 && p[2].1 == 3 && p[3].1 == 1);
}

#[verify::test]
pub fn test_clone_from_slice() {
    let src: [u32; 3] = [7, 8, 9];
    let mut dst: [u32; 3] = [0, 0, 0];
    dst.clone_from_slice(&src);
    assert!(dst[0] == 7 && dst[2] == 9);
}

#[verify::test]
pub fn test_iter_methods() {
    let v: [u32; 5] = [4, 8, 15, 16, 23];
    let mut it = v.iter();
    assert!(it.position(|x| *x > 10) == Some(2));
    assert!(it.next() == Some(&16));
    let mut it2 = v.iter();
    assert!(it2.rposition(|x| *x < 10) == Some(1));
    assert!(it2.next() == Some(&4));
    assert!(v.iter().any(|x| *x == 15));
    assert!(v.iter().all(|x| *x > 3));
    assert!(v.iter().find_map(|x| if *x > 15 { Some(*x * 2) } else { None }) == Some(32));
    assert!(v.iter().fold(0u32, |s, x| s + *x) == 66);
    let mut it3 = v.iter();
    assert!(it3.nth(3) == Some(&16));
    assert!(it3.len() == 1);
    assert!(it3.nth(3).is_none());
    assert!(v.iter().last() == Some(&23));
    assert!(v.iter().count() == 5);
    let (lo, hi) = v.iter().size_hint();
    assert!(lo == 5 && hi == Some(5));
}

#[verify::test]
pub fn test_range_inclusive_index() {
    let v: [u32; 5] = [1, 2, 3, 4, 5];
    let s = &v[1..=3];
    assert!(s.len() == 3 && s[0] == 2 && s[2] == 4);
    assert!(v.get(2..=4).is_some());
    assert!(v.get(3..=5).is_none());
    let mut w: [u32; 4] = [0, 0, 0, 0];
    w[1..=2].clone_from_slice(&v[..2]);
    assert!(w[1] == 1 && w[2] == 2 && w[3] == 0);
}

#[verify::test]
pub fn test_from_ref() {
    let x: u32 = 5;
    let s = core::slice::from_ref(&x);
    assert!(s.len() == 1 && s[0] == 5);
}

#[cfg(test)]
mod tests {
    #[test]
    fn all() {
        super::test_first_last();
        super::test_windows();
        super::test_array_windows();
        super::test_chunks_exact();
        super::test_binary_search();
        super::test_sort_unstable();
        super::test_clone_from_slice();
        super::test_iter_methods();
        super::test_range_inclusive_index();
        super::test_from_ref();
    }
}
