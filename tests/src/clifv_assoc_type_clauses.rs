//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Two associated types with the same bound (as in core::num::nonzero::
// ZeroablePrimitive or Cranelift's CompilePhase): the lifted parent clauses
// must get distinct field names.

pub trait Phase {
    type A: Copy;
    type B: Copy;
    fn first(a: Self::A, b: Self::B) -> Self::A;
}

pub struct P;

impl Phase for P {
    type A = u32;
    type B = u64;
    fn first(a: u32, _b: u64) -> u32 {
        a
    }
}

pub fn use_phase<T: Phase>(a: T::A, b: T::B) -> T::A {
    let c = a;
    T::first(c, b)
}

#[verify::test]
pub fn test_phase() {
    assert!(use_phase::<P>(3, 4) == 3);
}
