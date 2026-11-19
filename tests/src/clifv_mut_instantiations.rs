//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
//@ charon-args=--monomorphize-local-only
#![feature(register_tool)]
#![register_tool(verify)]
//! Library functions called with type parameters instantiated with mutable
//! borrows (`Option<&mut T>`, `Result<&mut T, E>`): the instantiated signature
//! has backward functions the generic one doesn't have, and the calls use the
//! models registered for those instantiations. The tests check that the values
//! written through the borrows are given back.
//! Expected values: Rust 1.96.

pub fn incr_if_let(v: &mut [u32], i: usize) {
    if let Some(x) = v.get_mut(i) {
        *x += 1;
    }
}

pub fn incr_unwrap(v: &mut [u32], i: usize) {
    let x = v.get_mut(i).unwrap();
    *x += 1;
}

pub fn incr_expect(v: &mut [u32], i: usize) {
    let x = v.get_mut(i).expect("in bounds");
    *x += 10;
}

pub fn incr_try(v: &mut [u32], i: usize) -> Option<u32> {
    let x = v.get_mut(i)?;
    *x += 100;
    Some(*x)
}

pub fn get_res(v: &mut [u32], i: usize) -> Result<&mut u32, u32> {
    match v.get_mut(i) {
        Some(x) => Ok(x),
        None => Err(0),
    }
}

pub fn incr_result_unwrap(v: &mut [u32], i: usize) {
    let x = get_res(v, i).unwrap();
    *x += 1000;
}

#[verify::test]
pub fn test_if_let() {
    let mut v = [1u32, 2, 3];
    incr_if_let(&mut v, 0);
    incr_if_let(&mut v, 3);
    assert!(v[0] == 2 && v[1] == 2 && v[2] == 3);
}

#[verify::test]
pub fn test_unwrap_expect() {
    let mut v = [1u32, 2, 3];
    incr_unwrap(&mut v, 1);
    assert!(v[0] == 1 && v[1] == 3 && v[2] == 3);
    incr_expect(&mut v, 2);
    assert!(v[0] == 1 && v[1] == 3 && v[2] == 13);
}

#[verify::test]
pub fn test_try() {
    let mut v = [1u32, 2, 3];
    assert!(incr_try(&mut v, 0) == Some(101));
    assert!(incr_try(&mut v, 3) == None);
    assert!(v[0] == 101 && v[1] == 2 && v[2] == 3);
}

#[verify::test]
pub fn test_result_unwrap() {
    let mut v = [1u32, 2, 3];
    incr_result_unwrap(&mut v, 2);
    assert!(v[0] == 1 && v[1] == 2 && v[2] == 1003);
}

#[cfg(test)]
mod tests {
    #[test]
    fn native() {
        super::test_if_let();
        super::test_unwrap_expect();
        super::test_try();
        super::test_result_unwrap();
    }
}
