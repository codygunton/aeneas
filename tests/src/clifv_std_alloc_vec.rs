//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Models of `alloc::vec`, `alloc::slice` and `alloc::boxed` items (Aeneas std library).

#[verify::test]
pub fn test_vec_basic() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    // capacity is not modelled beyond `capacity() >= len()`
    assert!(v.capacity() >= 4);
    v.reserve(10);
    assert!(v.try_reserve(10).is_ok());
    assert!(v.as_slice().len() == 4);
    let x = v.remove(1);
    assert!(x == 2);
    assert!(v[1] == 3);
    let p = v.pop();
    assert!(p.unwrap() == 4);
    assert!(v.len() == 2);
    let mut w: Vec<u32> = Vec::new();
    w.push(7);
    w.push(8);
    v.append(&mut w);
    assert!(w.len() == 0);
    assert!(v.len() == 4);
    assert!(v[3] == 8);
    v.retain(|e| *e != 3);
    assert!(v.len() == 3);
    assert!(v[0] == 1);
    assert!(v[1] == 7);
    v.clear();
    assert!(v.len() == 0);
    assert!(v.pop().is_none());
}

#[verify::test]
pub fn test_vec_mut_slice() {
    let mut v: Vec<u32> = Vec::new();
    v.push(5);
    v.push(6);
    let s = v.as_mut_slice();
    s[0] = 9;
    assert!(v[0] == 9);
    for e in &mut v {
        *e += 1;
    }
    assert!(v[0] == 10);
    assert!(v[1] == 7);
    let mut sum = 0;
    for e in &v {
        sum += *e;
    }
    assert!(sum == 17);
    let b: Box<[u32]> = v.into_boxed_slice();
    assert!(b.len() == 2);
}

#[verify::test]
pub fn test_vec_drain() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    v.push(5);
    let mut d = v.drain(1..3);
    assert!(d.size_hint().0 == 2);
    assert!(d.next().unwrap() == 2);
    assert!(d.next_back().unwrap() == 3);
    assert!(d.next().is_none());
    drop(d);
    assert!(v.len() == 3);
    assert!(v[1] == 4);
    let mut d2 = v.drain(..);
    assert!(d2.next().unwrap() == 1);
    drop(d2);
    assert!(v.len() == 0);
}

#[verify::test]
pub fn test_vec_traits() {
    let s: [u32; 3] = [3, 1, 2];
    let v: Vec<u32> = Vec::from(&s[..]);
    assert!(v.len() == 3);
    let mut w: Vec<u32> = Vec::default();
    w.extend(v.clone());
    w.extend(&s);
    assert!(w.len() == 6);
    assert!(w[3] == 3);
    assert!(v.cmp(&w) == core::cmp::Ordering::Less);
    assert!(w.cmp(&v) == core::cmp::Ordering::Greater);
    assert!(v.cmp(&v) == core::cmp::Ordering::Equal);
    let it = v.clone().into_iter();
    assert!(it.size_hint().0 == 3);
    assert!(v.clone().into_iter().count() == 3);
    assert!(v.clone().into_iter().last().unwrap() == 2);
    let total = v.into_iter().fold(0u32, |acc, e| acc * 10 + e);
    assert!(total == 312);
}

#[verify::test]
pub fn test_sort_by_key() {
    // Stable: equal keys keep their order.
    let mut v: Vec<(u32, u32)> = Vec::new();
    v.push((3, 0));
    v.push((1, 1));
    v.push((3, 2));
    v.push((2, 3));
    v.push((1, 4));
    v.sort_by_key(|p| p.0);
    assert!(v[0].1 == 1);
    assert!(v[1].1 == 4);
    assert!(v[2].1 == 3);
    assert!(v[3].1 == 0);
    assert!(v[4].1 == 2);
}

#[verify::test]
pub fn test_box_slice() {
    let s: [u32; 2] = [4, 5];
    let b: Box<[u32]> = Box::from(&s[..]);
    let c = b.clone();
    assert!(c.len() == 2);
    assert!(c[1] == 5);
    let d: Box<[u32]> = Box::default();
    assert!(d.len() == 0);
}

#[cfg(test)]
mod tests {
    #[test]
    fn all() {
        super::test_vec_basic();
        super::test_vec_mut_slice();
        super::test_vec_drain();
        super::test_vec_traits();
        super::test_sort_by_key();
        super::test_box_slice();
    }
}
