//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Nested borrows in the shape of Cranelift's ISLE lowering context
// (cranelift/codegen/src/machinst/isle.rs and machinst/lower.rs): a context
// holding `&'a mut Lower<'b>`, where `Lower<'b>` holds a `&'b Func`, used
// through the methods of a trait implemented on the context. The region `'b`
// only appears below shared borrows, so its backward function gives back
// nothing and is not synthesized.
//
// The methods of the implementation have a backward function for `'a`, which
// the trait declaration (where `Self` is opaque) can't express: the trait
// instance is not generated, and `lower` calls the methods directly.

pub struct Func {
    pub x: u32,
}

pub struct Lower<'f> {
    pub f: &'f Func,
    pub n: u32,
    pub v: Vec<u32>,
}

impl<'f> Lower<'f> {
    pub fn alloc(&mut self) -> u32 {
        self.n += 1;
        self.v.push(self.n);
        self.n + self.f.x
    }

    pub fn get(&self) -> u32 {
        self.n
    }
}

pub struct Backend {
    pub k: u32,
}

pub struct Ctx<'a, 'b> {
    pub lower_ctx: &'a mut Lower<'b>,
    pub backend: &'a Backend,
}

pub trait Context {
    fn alloc(&mut self) -> u32;
    fn k(&mut self) -> u32;
    fn wrapping_add(&mut self, a: u32, b: u32) -> u32;
    fn alloc_two(&mut self) -> u32;
}

/// Like `isle_prelude_methods!`: methods implemented by a macro expanded in
/// the implementation.
macro_rules! prelude_methods {
    () => {
        fn wrapping_add(&mut self, a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }

        fn alloc_two(&mut self) -> u32 {
            let a = self.alloc();
            let b = self.alloc();
            a + b
        }
    };
}

impl Context for Ctx<'_, '_> {
    fn alloc(&mut self) -> u32 {
        self.lower_ctx.alloc()
    }

    fn k(&mut self) -> u32 {
        self.backend.k + self.lower_ctx.get()
    }

    prelude_methods!();
}

/// Like `isle::lower`: build the context, then call the trait methods on it.
pub fn lower(l: &mut Lower, b: &Backend) -> u32 {
    let mut c = Ctx {
        lower_ctx: l,
        backend: b,
    };
    let a = c.alloc();
    let b = c.alloc();
    let k = c.k();
    let s = c.wrapping_add(a + b, k);
    s + c.alloc_two()
}

#[verify::test]
pub fn test_lower() {
    // Rust results: the first two `alloc` return 11 and 12, `k` returns
    // 100 + 2, `alloc_two` returns 13 + 14: 11 + 12 + 102 + 27 = 152, and `n`
    // was incremented four times.
    let f = Func { x: 10 };
    let mut l = Lower {
        f: &f,
        n: 0,
        v: Vec::new(),
    };
    let b = Backend { k: 100 };
    let r = lower(&mut l, &b);
    assert!(r == 152);
    assert!(l.n == 4);
    assert!(l.v.len() == 4);
    assert!(l.v[3] == 4);
}

#[verify::test]
pub fn test_lower_twice() {
    // Rust results: the second call starts from n = 4: 15 + 16 + 106 + 35 = 172.
    let f = Func { x: 10 };
    let mut l = Lower {
        f: &f,
        n: 0,
        v: Vec::new(),
    };
    let b = Backend { k: 100 };
    let r1 = lower(&mut l, &b);
    let r2 = lower(&mut l, &b);
    assert!(r1 == 152);
    assert!(r2 == 172);
    assert!(l.n == 8);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_lower() {
        super::test_lower();
    }
    #[test]
    fn test_lower_twice() {
        super::test_lower_twice();
    }
}
