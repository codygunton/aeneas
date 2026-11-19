//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Static borrows hidden in ADTs, in the shape of Cranelift's
// `SigSet::new` (cranelift/codegen/src/machinst/abi.rs): the function holds
// `AliasRegionData { description: Cow<'static, str> }` values, so a
// `&Func` contains static borrows below a shared borrow, and the loop calling a
// `&mut self` method with a reborrow `&func.dfg` creates region abstractions
// for the static region holding nested shared borrows, which the joins must
// destructure.
use std::borrow::Cow;

pub struct Region {
    pub id: u32,
    pub description: Cow<'static, str>,
}

pub struct Dfg {
    pub sigs: Vec<u32>,
    pub regions: Vec<Region>,
}

pub struct Func {
    pub sig: u32,
    pub dfg: Dfg,
}

pub struct Flags {
    pub b: bool,
}

pub enum Err {
    Bad(u32),
    Other,
}

pub struct SigSet {
    pub v: Vec<u32>,
}

impl SigSet {
    fn add_ref(&mut self, i: usize, dfg: &Dfg, flags: &Flags) -> Result<u32, Err> {
        let s = dfg.sigs[i];
        if flags.b && s == 0 {
            return Err(Err::Bad(s));
        }
        self.v.push(s);
        Ok(s)
    }

    pub fn new(func: &Func, flags: &Flags) -> Result<Self, Err> {
        let mut sigs = SigSet { v: Vec::new() };
        sigs.v.push(func.sig);
        for i in 0..func.dfg.sigs.len() {
            sigs.add_ref(i, &func.dfg, flags)?;
        }
        Ok(sigs)
    }
}

fn mk_func(sigs: Vec<u32>) -> Func {
    Func {
        sig: 7,
        dfg: Dfg {
            sigs,
            regions: Vec::new(),
        },
    }
}

#[verify::test]
pub fn test_sigset_ok() {
    // Rust results: the signature 7, then the three signatures in order.
    let f = mk_func(vec![1, 0, 3]);
    let flags = Flags { b: false };
    match SigSet::new(&f, &flags) {
        Ok(s) => {
            assert!(s.v.len() == 4);
            assert!(s.v[0] == 7);
            assert!(s.v[2] == 0);
            assert!(s.v[3] == 3);
        }
        Err(_) => assert!(false),
    }
}

#[verify::test]
pub fn test_sigset_err() {
    // Rust results: the second signature is 0 with the flag set: error 0.
    let f = mk_func(vec![1, 0, 3]);
    let flags = Flags { b: true };
    match SigSet::new(&f, &flags) {
        Ok(_) => assert!(false),
        Err(Err::Bad(s)) => assert!(s == 0),
        Err(Err::Other) => assert!(false),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sigset_ok() {
        super::test_sigset_ok();
    }
    #[test]
    fn test_sigset_err() {
        super::test_sigset_err();
    }
}
