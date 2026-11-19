//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Nested matches with non-trivial fallbacks, with early returns (as in
// Cranelift's ISLE lowering and the CLIF parser): the inner match is rewritten
// with a fallback flag first, then the outer match, whose branches now mention
// the inner flag (a local which didn't exist in the original body).

#[derive(Clone, Copy)]
pub enum Op {
    A,
    B,
    C,
    D,
    E,
}

pub fn lower(op: Op, inner: Op, x: u32) -> u32 {
    // Four branchings with early returns followed by more code: the function
    // gets a return carrier, which enables the fallback hoisting.
    if x == 1000 {
        return 0;
    }
    if x == 1001 {
        return 1;
    }
    if x == 1002 {
        return 2;
    }
    if x == 1003 {
        return 3;
    }
    let y = match op {
        Op::A => match inner {
            Op::B => {
                if x > 3 {
                    return x - 3;
                }
                10
            }
            _ => {
                let z = x.wrapping_mul(7);
                z.wrapping_add(1)
            }
        },
        _ => {
            let z = x.wrapping_mul(5);
            z.wrapping_add(2)
        }
    };
    y + 100
}

#[verify::test]
pub fn test_lower() {
    // Rust results: lower(A, B, 5) = 2 (early return), lower(A, B, 1) = 110,
    // lower(A, C, 2) = 115, lower(D, A, 3) = 117.
    assert!(lower(Op::A, Op::B, 5) == 2);
    assert!(lower(Op::A, Op::B, 1) == 110);
    assert!(lower(Op::A, Op::C, 2) == 115);
    assert!(lower(Op::D, Op::A, 3) == 117);
}
