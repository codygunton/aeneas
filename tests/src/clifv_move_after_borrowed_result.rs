//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// The shape of the extraction entry point `compile_aarch64`: a method
// returning `Result<&'a T, E<'a>>` borrowed from `&'a mut self`, `map_err`
// with a closure dropping the borrow, `?`, reads through the returned
// reference, then a move out of a field of the (no longer borrowed) struct.

pub struct Func {
    pub v: Vec<u32>,
}

pub struct Code {
    pub n: u32,
    pub bytes: Vec<u8>,
}

pub struct Ctx {
    pub func: Func,
    pub code: Code,
}

pub struct CErr<'a> {
    pub func: &'a Func,
    pub inner: u32,
}

impl Ctx {
    pub fn compile(&mut self, x: u32) -> Result<&Code, CErr<'_>> {
        if x == 0 {
            return Err(CErr {
                func: &self.func,
                inner: 7,
            });
        }
        self.code.n = x;
        self.func.v.push(x);
        Ok(&self.code)
    }
}

pub enum Failure {
    Codegen(u32),
}

pub struct Artifact {
    pub n: u32,
    pub len: usize,
    pub func: Func,
}

pub fn entry(x: u32) -> Result<Artifact, Failure> {
    let mut ctx = Ctx {
        func: Func { v: Vec::new() },
        code: Code {
            n: 0,
            bytes: Vec::new(),
        },
    };
    let compiled = ctx
        .compile(x)
        .map_err(|e| Failure::Codegen(e.inner))?;
    let n = compiled.n;
    let len = compiled.bytes.len();
    Ok(Artifact {
        n,
        len,
        func: ctx.func,
    })
}

pub fn check() -> bool {
    let ok = match entry(3) {
        Ok(a) => a.n == 3 && a.len == 0 && a.func.v.len() == 1,
        Err(_) => false,
    };
    let err = match entry(0) {
        Ok(_) => false,
        Err(Failure::Codegen(e)) => e == 7,
    };
    ok && err
}

#[verify::test]
pub fn test_entry() {
    assert!(check());
}
