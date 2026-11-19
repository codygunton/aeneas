//@ [!lean] skip
//@ charon-args=--no-code-duplication
#![feature(register_tool)]
#![register_tool(verify)]
// ISLE-style rule chains (as in Cranelift's generated lowering code): each rule
// that does not match falls through to the next one. Reconstructed without code
// duplication, every fall-through point is a `loop { ...; break }` block
// around the previous rules, nested once per rule. Such a block never
// continues: its body is evaluated once, which keeps the translation linear in
// the nesting depth (instead of exponential).

pub fn rules(x: u32) -> u32 {
    if let Some(a) = x.checked_sub(0) {
        if a % 2 == 0 {
            if a > 0 {
                return a + 0;
            }
        }
    }
    if let Some(a) = x.checked_sub(1) {
        if a % 3 == 0 {
            if a > 3 {
                return a + 1;
            }
        }
    }
    if let Some(a) = x.checked_sub(2) {
        if a % 4 == 0 {
            if a > 6 {
                return a + 2;
            }
        }
    }
    if let Some(a) = x.checked_sub(3) {
        if a % 5 == 0 {
            if a > 9 {
                return a + 3;
            }
        }
    }
    if let Some(a) = x.checked_sub(4) {
        if a % 6 == 0 {
            if a > 12 {
                return a + 4;
            }
        }
    }
    if let Some(a) = x.checked_sub(5) {
        if a % 7 == 0 {
            if a > 15 {
                return a + 5;
            }
        }
    }
    if let Some(a) = x.checked_sub(6) {
        if a % 8 == 0 {
            if a > 18 {
                return a + 6;
            }
        }
    }
    if let Some(a) = x.checked_sub(7) {
        if a % 9 == 0 {
            if a > 21 {
                return a + 7;
            }
        }
    }
    if let Some(a) = x.checked_sub(8) {
        if a % 10 == 0 {
            if a > 24 {
                return a + 8;
            }
        }
    }
    if let Some(a) = x.checked_sub(9) {
        if a % 11 == 0 {
            if a > 27 {
                return a + 9;
            }
        }
    }
    if let Some(a) = x.checked_sub(10) {
        if a % 12 == 0 {
            if a > 30 {
                return a + 10;
            }
        }
    }
    if let Some(a) = x.checked_sub(11) {
        if a % 13 == 0 {
            if a > 33 {
                return a + 11;
            }
        }
    }
    0
}

#[verify::test]
pub fn test_rules() {
    // Rust results: rules(10) = 10 (rule 0); rules(0) = 0 (no rule); rules(7) = 7.
    assert!(rules(10) == 10);
    assert!(rules(0) == 0);
    assert!(rules(7) == 7);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_rules() {
        super::test_rules();
    }
}
