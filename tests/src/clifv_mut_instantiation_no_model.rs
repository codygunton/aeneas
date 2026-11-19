//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] continue-on-error
#![feature(register_tool)]
#![register_tool(verify)]
//! A call instantiating the generics of a function with mutable borrows such that the call needs
//! backward functions the signature of the function doesn't have, without a model for this
//! instantiation, is an error (the caller becomes an `opaque` stub) rather than ill-typed code
//! dropping the values written through the borrows.

/// Generic local function: its translation has no backward function.
pub fn id<T>(x: T) -> T {
    x
}

pub fn incr_id(x: &mut u32) {
    let y = id(x);
    *y += 1;
}

/// Library function without a model for `Option<&mut T>`.
pub fn incr_ok_or(v: &mut [u32], i: usize) -> Result<(), u32> {
    let x = v.get_mut(i).ok_or(0u32)?;
    *x += 1;
    Ok(())
}

/// Not affected.
#[verify::test]
pub fn test_unaffected() {
    let mut x = 1u32;
    let y = &mut x;
    *y += 1;
    assert!(x == 2);
}
