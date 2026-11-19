//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Branchings whose branches contain complete inner loops (with breaks
// targeting those loops only), followed by more code. The `break`s don't
// escape the branches, so the contexts are joined after each branching:
// the translation stays linear in the number of branchings (it was
// exponential when any nested `break` prevented the join).

pub fn chain(x: u32) -> u32 {
    let mut s: u32 = 0;
    if x % 2 == 0 {
        let mut i = 0;
        while i < 1 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 3 == 0 {
        let mut i = 0;
        while i < 2 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 4 == 0 {
        let mut i = 0;
        while i < 3 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 5 == 0 {
        let mut i = 0;
        while i < 4 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 6 == 0 {
        let mut i = 0;
        while i < 5 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 7 == 0 {
        let mut i = 0;
        while i < 6 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 8 == 0 {
        let mut i = 0;
        while i < 7 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 9 == 0 {
        let mut i = 0;
        while i < 8 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 10 == 0 {
        let mut i = 0;
        while i < 9 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 11 == 0 {
        let mut i = 0;
        while i < 10 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 12 == 0 {
        let mut i = 0;
        while i < 11 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 13 == 0 {
        let mut i = 0;
        while i < 12 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 14 == 0 {
        let mut i = 0;
        while i < 13 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 15 == 0 {
        let mut i = 0;
        while i < 14 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 16 == 0 {
        let mut i = 0;
        while i < 15 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    if x % 17 == 0 {
        let mut i = 0;
        while i < 16 {
            if i == x {
                break;
            }
            s = s.wrapping_add(i);
            i += 1;
        }
    }
    s
}

#[verify::test]
pub fn test_chain() {
    // Rust results: chain(0) = 0 (every loop breaks at i == 0); chain(1) = 0
    // (no branch taken); chain(12) = 69 (x % 2, 3, 4, 6, 12 == 0: sums of
    // 0..1, 0..2, 0..3, 0..5, 0..11 = 0 + 1 + 3 + 10 + 55).
    assert!(chain(0) == 0);
    assert!(chain(1) == 0);
    assert!(chain(12) == 69);
}
