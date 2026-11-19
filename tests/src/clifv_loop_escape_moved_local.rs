//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Early returns from nested loops which move a local that the normal exit path
// still uses after the loops (the returned value is computed after the exit of
// the lowered loops, see `lower_loop_exits`).

pub struct P {
    pub a: u32,
    pub b: u32,
}

/// The value is moved out of `r` by the early return, and `r` is returned after
/// the loops.
pub fn find(n: u32, target: u32) -> P {
    let mut r = P { a: 0, b: 0 };
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            if i * j == target {
                r.a = i;
                r.b = j;
                return r;
            }
            j += 1;
        }
        r.a += 1;
        i += 1;
    }
    r
}

/// The returned value is built from a temporary and from a local which is
/// used after the inner loop.
pub fn find_sum(n: u32, target: u32) -> Option<P> {
    let mut acc = P { a: 0, b: 0 };
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            acc.b += j;
            if acc.b == target {
                let t = i + j;
                return Some(P { a: t, b: acc.b });
            }
            if acc.b > target {
                return None;
            }
            j += 1;
        }
        acc.a += acc.b;
        i += 1;
    }
    Some(acc)
}

/// Three nested loops, the return moves a local which the middle loop reads
/// after the innermost one.
pub fn find3(n: u32) -> P {
    let mut r = P { a: 0, b: 0 };
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            let mut k = 0;
            while k < n {
                if i + j + k == 7 && i * j * k == 12 {
                    r.a = i * 100 + j * 10 + k;
                    return r;
                }
                k += 1;
            }
            r.b += 1;
            j += 1;
        }
        i += 1;
    }
    r
}

#[verify::test]
pub fn test_find() {
    // Rust results: 12 = 2 * 6 (i = 2, j = 6); no pair for 13 below 5.
    let r = find(10, 12);
    assert!(r.a == 2 && r.b == 6);
    let r = find(5, 13);
    assert!(r.a == 5 && r.b == 0);
}

/// `a * 100 + b`, or `u32::MAX` for `None`
pub fn code(r: &Option<P>) -> u32 {
    match r {
        Some(p) => p.a * 100 + p.b,
        None => u32::MAX,
    }
}

#[verify::test]
pub fn test_find_sum() {
    // Rust results: acc.b reaches 6 at i = 0, j = 3 (Some { a: 3, b: 6 }); 7
    // is skipped (6 then 10: None); with n = 2 the sum never reaches 100:
    // Some { a: 3, b: 2 }.
    assert!(code(&find_sum(10, 6)) == 306);
    assert!(code(&find_sum(10, 7)) == u32::MAX);
    assert!(code(&find_sum(2, 100)) == 302);
}

#[verify::test]
pub fn test_find3() {
    // Rust results: (2, 2, 3) is the first triple with sum 7 and product 12,
    // after 12 increments of r.b (5 for i = 0, 5 for i = 1, 2 for i = 2).
    let r = find3(5);
    assert!(r.a == 223 && r.b == 12);
    let r = find3(2);
    assert!(r.a == 0 && r.b == 4);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_find() {
        super::test_find();
    }
    #[test]
    fn test_find_sum() {
        super::test_find_sum();
    }
    #[test]
    fn test_find3() {
        super::test_find3();
    }
}
