//@ [!lean] skip
//@ charon-args=--code-duplication-limit 2 --monomorphize-local-only
#![feature(register_tool)]
#![register_tool(verify)]
// A region abstraction holding a projected shared borrow (`get` takes a shared
// borrow of a value which itself contains a shared borrow), alive across an
// `if` and a loop: the collapse of the joined contexts must register the
// projected shared borrows of the abstraction (InterpMatchCtxs.ml, "Internal
// error" in `compute_abs_borrows_loans_maps` before the fix).

pub struct Wrap<'b> {
    pub r: &'b u32,
    pub n: u32,
}

pub fn get<'a, 'b>(w: &'a Wrap<'b>) -> &'a u32 {
    w.r
}

pub fn f(x: &u32, c: &mut u32) -> u32 {
    let w = Wrap { r: x, n: 3 };
    let y = get(&w);
    if *c > 3 {
        *c += 1;
    }
    let mut s = *y;
    let mut i = 0;
    while i < *c {
        s += *y;
        i += 1;
    }
    s + w.n
}

#[verify::test]
pub fn test_f() {
    // Rust results: 5 + 2 * 5 + 3 = 18 (c unchanged), 5 + 5 * 5 + 3 = 33
    // (c: 4 -> 5).
    let x = 5;
    let mut c = 2;
    assert!(f(&x, &mut c) == 18);
    assert!(c == 2);
    let mut d = 4;
    assert!(f(&x, &mut d) == 33);
    assert!(d == 5);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_f() {
        super::test_f();
    }
}
