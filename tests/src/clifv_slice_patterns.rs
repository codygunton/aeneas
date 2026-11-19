//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Slice patterns, whose length test MIR writes as a read of the metadata of
// the slice pointer: on a reference (`VRegAllocator::alloc` in Cranelift's
// machinst/vcode.rs) and on a raw pointer to the payload of an `Option`
// (`while let Some([rt, rt2]) = iter.next()` in `gen_clobber_restore`,
// isa/aarch64/abi.rs). The pre-pass uses the declaration of
// `core::slice::len`, which `count` brings into the crate.

pub fn count(classes: &[u8]) -> usize {
    classes.len()
}

pub fn regs(classes: &[u8]) -> Option<(u8, u8)> {
    match classes {
        &[c0] => Some((c0, 0)),
        &[c0, c1] => Some((c0, c1)),
        _ => None,
    }
}

pub fn pair_sum(chunk: Option<&[u32]>) -> u32 {
    if let Some([a, b]) = chunk {
        *a + *b
    } else {
        0
    }
}

#[verify::test]
pub fn test_slice_patterns() {
    assert!(regs(&[]).is_none());
    assert!(regs(&[3]) == Some((3, 0)));
    assert!(regs(&[3, 4]) == Some((3, 4)));
    assert!(regs(&[3, 4, 5]).is_none());
    assert!(pair_sum(Some(&[1, 2])) == 3);
    assert!(pair_sum(Some(&[1, 2, 3])) == 0);
    assert!(pair_sum(None) == 0);
    assert!(count(&[1, 2]) == 2);
}
