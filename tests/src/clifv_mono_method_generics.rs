//@ [!lean] skip
//@ charon-args=--monomorphize-local-only
#![feature(register_tool)]
#![register_tool(verify)]
// A trait method with its own generics, monomorphized for two instantiations (Cranelift's
// `MachInst::get_operands`, called with several operand visitors): the two instances of the
// impl method must get different names.

pub trait Visit {
    fn visit<F: FnMut(u32) -> u32>(&self, f: &mut F) -> u32;
}

pub struct Pair {
    pub a: u32,
    pub b: u32,
}

impl Visit for Pair {
    fn visit<F: FnMut(u32) -> u32>(&self, f: &mut F) -> u32 {
        f(self.a) + f(self.b)
    }
}

pub fn sum(p: &Pair) -> u32 {
    p.visit(&mut |x| x)
}

pub fn sum_doubled(p: &Pair) -> u32 {
    p.visit(&mut |x| 2 * x)
}

#[verify::test]
pub fn test_visit() {
    let p = Pair { a: 1, b: 2 };
    assert!(sum(&p) == 3);
    assert!(sum_doubled(&p) == 6);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_visit() {
        super::test_visit();
    }
}
