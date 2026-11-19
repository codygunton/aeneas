#![feature(register_tool)]
#![register_tool(verify)]
// See `dep/src/lib.rs`.
use clifv_or_pattern_ref_bindings_dep::{bump_args, sum_args, Data};

#[verify::test]
fn test_arguments() {
    assert!(sum_args(&Data::Nullary { x: 5 }) == 0);
    assert!(sum_args(&Data::Unary { arg: 4, imm: 1 }) == 4);
    assert!(sum_args(&Data::Load { arg: 6 }) == 6);
    assert!(sum_args(&Data::Binary { args: [1, 2] }) == 3);
    assert!(sum_args(&Data::Store { args: [3, 4], off: -1 }) == 7);
    assert!(sum_args(&Data::Ternary { args: [1, 2, 3] }) == 6);
    assert!(sum_args(&Data::Cas { args: [4, 5, 6] }) == 15);
    assert!(sum_args(&Data::Multi { args: vec![10, 20] }) == 30);
    assert!(sum_args(&Data::Call { args: vec![7], callee: 2 }) == 7);
}

#[verify::test]
fn test_arguments_mut() {
    assert!(bump_args(Data::Nullary { x: 5 }) == 0);
    assert!(bump_args(Data::Load { arg: 6 }) == 7);
    assert!(bump_args(Data::Store { args: [3, 4], off: -1 }) == 9);
    assert!(bump_args(Data::Cas { args: [4, 5, 6] }) == 18);
    assert!(bump_args(Data::Call { args: vec![7], callee: 2 }) == 8);
}
