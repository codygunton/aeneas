//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// An enumeration with a variant named `Result` (Cranelift's `ValueDef::Result`): its methods are
// declared in its namespace, where the constructor would shadow the `Result` monad of their
// signatures, so the constructor is renamed `Result_`.

pub enum ValueDef {
    Result(u32, usize),
    Param(u32, usize),
}

impl ValueDef {
    pub fn inst(&self) -> Option<u32> {
        match *self {
            ValueDef::Result(inst, _) => Some(inst),
            _ => None,
        }
    }
}

#[verify::test]
pub fn test_inst() {
    assert!(ValueDef::Result(3, 0).inst() == Some(3));
    assert!(ValueDef::Param(4, 1).inst().is_none());
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_inst() {
        super::test_inst();
    }
}
