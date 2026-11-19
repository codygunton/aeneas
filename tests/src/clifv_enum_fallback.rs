//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// ISLE-style rule chains testing one variant of a large enumeration at a
// time, with a fallthrough for every other variant. The fallthrough is
// evaluated once with the scrutinee left unexpanded (a `_` pattern), instead
// of once per remaining variant.

#[derive(Clone, Copy)]
pub enum Op {
    V0,
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    V9,
    V10,
    V11,
}

pub fn rules(op: &Op, x: u32) -> u32 {
    if let Op::V0 = op {
        if x > 0 {
            return x - 0;
        }
    }
    if let Op::V1 = op {
        if x > 1 {
            return x - 1;
        }
    }
    if let Op::V2 = op {
        if x > 2 {
            return x - 2;
        }
    }
    if let Op::V3 = op {
        if x > 3 {
            return x - 3;
        }
    }
    if let Op::V4 = op {
        if x > 4 {
            return x - 4;
        }
    }
    if let Op::V5 = op {
        if x > 5 {
            return x - 5;
        }
    }
    if let Op::V6 = op {
        if x > 6 {
            return x - 6;
        }
    }
    if let Op::V7 = op {
        if x > 7 {
            return x - 7;
        }
    }
    if let Op::V8 = op {
        if x > 8 {
            return x - 8;
        }
    }
    if let Op::V9 = op {
        if x > 9 {
            return x - 9;
        }
    }
    x + 100
}

// More than 512 locals: the locals with disjoint live ranges are coalesced.
pub fn many_locals(x: u32) -> u32 {
    let mut s: u32 = x;
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(8).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(2).wrapping_add(x.wrapping_shr(4));
    s = s.wrapping_mul(3).wrapping_add(x.wrapping_shr(0));
    s = s.wrapping_mul(4).wrapping_add(x.wrapping_shr(1));
    s = s.wrapping_mul(5).wrapping_add(x.wrapping_shr(2));
    s = s.wrapping_mul(6).wrapping_add(x.wrapping_shr(3));
    s = s.wrapping_mul(7).wrapping_add(x.wrapping_shr(4));
    s
}

#[verify::test]
pub fn test_rules() {
    // Rust results: 7, 102, 105, 3393591880.
    assert!(rules(&Op::V3, 10) == 7);
    assert!(rules(&Op::V3, 2) == 102);
    assert!(rules(&Op::V11, 5) == 105);
    assert!(many_locals(1) == 3393591880);
}
