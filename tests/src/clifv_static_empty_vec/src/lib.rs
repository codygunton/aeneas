#![feature(register_tool)]
#![register_tool(verify)]
// See `dep/src/lib.rs`. The lowering of the empty `Vec` built by the static
// initializers calls `Vec::new`, which must be in the crate (as in Cranelift).
use clifv_static_empty_vec_dep::get_env;

pub fn summary(pinned: bool) -> u64 {
    let env = get_env(pinned);
    let scratch = if env.scratch[2].is_none() { 1000 } else { 0 };
    env.preferred[0] + env.preferred[1] * 10 + env.fixed.len() as u64 * 100 + scratch
}

pub fn fresh() -> Vec<u8> {
    Vec::new()
}

#[verify::test]
fn test_summary() {
    assert!(summary(true) == 1021);
    assert!(summary(false) == 1043);
}
