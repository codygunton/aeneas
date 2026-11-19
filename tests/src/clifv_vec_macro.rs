//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// `vec![..]` with elements lowers to `Box::new_uninit()`, a write of the array
// through `MaybeUninit`'s fields, `assume_init` and `into_vec` (the shape of
// `MInst::gen_nop_units` and `SpanningTree::new` in Cranelift).

pub fn nop_units() -> Vec<Vec<u8>> {
    vec![vec![0x1f, 0x20, 0x03, 0xd5]]
}

pub fn pair(a: u32, b: u32) -> Vec<u32> {
    vec![a, b, a + b]
}

pub fn boxed(x: u64) -> Box<u64> {
    Box::new(x)
}

#[verify::test]
pub fn test_vec_macro() {
    let v = nop_units();
    assert!(v.len() == 1);
    assert!(v[0].len() == 4);
    assert!(v[0][0] == 0x1f);
    assert!(v[0][3] == 0xd5);
    let p = pair(3, 4);
    assert!(p.len() == 3);
    assert!(p[2] == 7);
    assert!(*boxed(9) == 9);
}
