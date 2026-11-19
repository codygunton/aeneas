//@ [!lean] skip
//@ charon-args=--monomorphize-local-only
#![feature(register_tool)]
#![register_tool(verify)]
// Local-only monomorphized LLBC (`charon --preset=aeneas
// --monomorphize-local-only`): local items are instantiated per use, standard
// library items (`Vec`, `Box`, `Option`, slices) stay polymorphic and extract
// to the generic Aeneas library models.

#[derive(Clone, Copy)]
pub struct Nop {
    pub x: u32,
}

pub fn vec_push_len(n: u32) -> usize {
    let mut v: Vec<Nop> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(Nop { x: i });
        i += 1;
    }
    v.len()
}

pub fn vec_index(v: &Vec<u64>, i: usize) -> u64 {
    v[i]
}

pub fn vec_index_mut(v: &mut Vec<u64>, i: usize, x: u64) {
    v[i] = x;
}

pub fn boxed(x: Nop) -> Box<Nop> {
    Box::new(x)
}

pub fn unbox(b: Box<Nop>) -> u32 {
    (*b).x
}

pub fn opt_get(o: Option<Nop>) -> u32 {
    match o {
        Some(n) => n.x,
        None => 0,
    }
}

pub fn opt_unwrap_or(o: Option<u32>, d: u32) -> u32 {
    o.unwrap_or(d)
}

/// `Option::map` stays polymorphic and takes the (local, monomorphic) closure's
/// `FnOnce` implementation.
pub fn opt_map(o: Option<Nop>) -> Option<u32> {
    o.map(|n| n.x + 1)
}

/// A local generic function calling the standard `Clone` trait: instantiated
/// with `Nop`, it calls the local `impl Clone for Nop`.
pub fn dup<T: Clone>(x: &T) -> T {
    x.clone()
}

pub fn dup_nop(n: Nop) -> u32 {
    dup(&n).x
}

pub fn slice_sum(s: &[u32]) -> u32 {
    let mut acc = 0;
    let mut i = 0;
    while i < s.len() {
        acc += s[i];
        i += 1;
    }
    acc
}

pub fn slice_first(s: &[Nop]) -> u32 {
    match s.get(0) {
        Some(n) => n.x,
        None => 0,
    }
}

pub fn array_to_slice(a: &[u32; 3]) -> u32 {
    slice_sum(a)
}

pub fn vec_deref_sum(v: &Vec<u32>) -> u32 {
    slice_sum(v)
}

#[verify::test]
pub fn test_vec() {
    // Rust results: 3; v[1] = 20 then 7.
    assert!(vec_push_len(3) == 3);
    let mut v: Vec<u64> = Vec::new();
    v.push(10);
    v.push(20);
    assert!(vec_index(&v, 1) == 20);
    vec_index_mut(&mut v, 1, 7);
    assert!(vec_index(&v, 1) == 7);
}

#[verify::test]
pub fn test_box() {
    // Rust result: 5.
    assert!(unbox(boxed(Nop { x: 5 })) == 5);
}

#[verify::test]
pub fn test_option() {
    // Rust results: 4, 0, 9, 1, 5, 0, 6.
    assert!(opt_get(Some(Nop { x: 4 })) == 4);
    assert!(opt_get(None) == 0);
    assert!(opt_unwrap_or(Some(9), 1) == 9);
    assert!(opt_unwrap_or(None, 1) == 1);
    assert!(opt_unwrap_or(opt_map(Some(Nop { x: 4 })), 0) == 5);
    assert!(opt_unwrap_or(opt_map(None), 0) == 0);
    assert!(dup_nop(Nop { x: 6 }) == 6);
}

#[verify::test]
pub fn test_slices() {
    // Rust results: 6, 6, 8, 0.
    let a: [u32; 3] = [1, 2, 3];
    assert!(array_to_slice(&a) == 6);
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(5);
    assert!(vec_deref_sum(&v) == 6);
    let ns: [Nop; 2] = [Nop { x: 8 }, Nop { x: 9 }];
    assert!(slice_first(&ns) == 8);
    let empty: [Nop; 0] = [];
    assert!(slice_first(&empty) == 0);
}

#[cfg(test)]
mod tests {
    #[test]
    fn run() {
        super::test_vec();
        super::test_box();
        super::test_option();
        super::test_slices();
    }
}
