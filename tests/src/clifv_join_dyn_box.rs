//@ [!lean] skip
//@ charon-args=--code-duplication-limit 2 --monomorphize-local-only
#![feature(register_tool)]
#![register_tool(verify)]
// A `Box<dyn Any>` alive in a block whose `?` exits run its drop before
// returning. This is the shape of `Context::compile_stencil` (cranelift
// `context.rs`): `let _tt = timing::compile();` returns a `Box<dyn Any>` when
// the `timing` feature is off, and the `?` exits of the block become a loop
// whose fixed point must be checked, which matches the `dyn` types.
use std::any::Any;

pub struct Error(pub u32);

pub struct Stencil {
    pub code: Vec<u32>,
}

pub fn enabled() -> bool {
    false
}

pub fn log(_c: &u32) {}

pub fn check(x: u32) -> Result<(), Error> {
    if x > 10 { Err(Error(x)) } else { Ok(()) }
}

pub fn token() -> Box<dyn Any> {
    Box::new(())
}

pub fn make(c: &u32) -> Result<Stencil, Error> {
    if *c > 5 { Err(Error(*c)) } else { Ok(Stencil { code: vec![*c * 2] }) }
}

pub fn first(s: &Stencil) -> u32 {
    s.code[0]
}

pub fn compile(c: &mut u32) -> Result<Stencil, Error> {
    let result;
    if enabled() {
        log(c);
    }
    {
        let _tt = token();
        check(*c)?;
        *c += 1;
        check(*c)?;
        result = make(c);
    }
    if enabled() {
        log(c);
    }
    result
}

/// A loop (which continues) whose fixed point is checked while a
/// `Box<dyn Any>` is alive.
pub fn count(c: &mut u32, n: u32) -> u32 {
    let _tt = token();
    let mut s = 0;
    while *c < n {
        s += *c;
        *c += 1;
    }
    s
}

pub fn summary(r: &Result<Stencil, Error>) -> u32 {
    match r {
        Ok(s) => first(s),
        Err(Error(e)) => 1000 + *e,
    }
}

#[verify::test]
pub fn test_compile() {
    // Rust results: Ok([8]) (c: 3 -> 4), Err(11) (c: 10 -> 11), Err(12)
    // (c unchanged), Err(6) from `make` (c: 5 -> 6).
    let mut c = 3;
    assert!(summary(&compile(&mut c)) == 8);
    assert!(c == 4);
    let mut d = 10;
    assert!(summary(&compile(&mut d)) == 1011);
    assert!(d == 11);
    let mut e = 12;
    assert!(summary(&compile(&mut e)) == 1012);
    assert!(e == 12);
    let mut f = 5;
    assert!(summary(&compile(&mut f)) == 1006);
    assert!(f == 6);
    let mut g = 2;
    assert!(count(&mut g, 5) == 9);
    assert!(g == 5);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_compile() {
        super::test_compile();
    }
}
