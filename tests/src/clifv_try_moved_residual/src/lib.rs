#![feature(register_tool)]
#![register_tool(verify)]
// See `dep/src/lib.rs`.
use clifv_try_moved_residual_dep::run;

#[verify::test]
fn test_run() {
    assert!(run(0) == 0);
    assert!(run(2) == 20);
    assert!(run(5) == 100);
}
