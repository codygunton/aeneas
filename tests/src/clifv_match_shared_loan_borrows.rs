//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// A region abstraction holding a shared loan of a value which contains
// (`'static`) shared borrows, alive across an `if` whose branches must be
// joined. This is the shape of `Context::compile_stencil(&mut self, isa: &dyn
// TargetIsa, ..)` once `TargetIsa` is devirtualized to `AArch64Backend`: the
// backend contains a `target_lexicon::Triple`, whose `Vendor` may be
// `Custom(CustomVendor::Static(&'static str))`.

pub enum Vendor {
    Unknown,
    Custom(&'static str),
}

pub struct Backend {
    pub vendor: Vendor,
    pub x: u32,
}

pub fn reborrow<'a>(b: &'a Backend) -> &'a Backend {
    b
}

pub fn vendor_len(b: &Backend) -> u32 {
    b.x / 3
}

pub fn incr(c: &mut u32) {
    *c += 1;
}

pub fn compile(b: &Backend, c: &mut u32) -> u32 {
    let r = reborrow(b);
    if *c > 3 {
        incr(c);
    }
    r.x + vendor_len(r) + *c
}

#[verify::test]
pub fn test_compile() {
    // Rust results: 10 + 3 + 5 = 18 (c: 4 -> 5), then 10 + 3 + 1 = 14.
    let b = Backend {
        vendor: Vendor::Custom("abc"),
        x: 10,
    };
    let mut c = 4;
    assert!(compile(&b, &mut c) == 18);
    assert!(c == 5);
    let mut d = 1;
    assert!(compile(&b, &mut d) == 14);
    assert!(d == 1);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_compile() {
        super::test_compile();
    }
}
