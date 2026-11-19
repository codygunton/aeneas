//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// The shape of the `log` macros (`log::trace!` and friends, used by Cranelift's
// `trace!`): inside an `if`, a call receives a shared borrow of a tuple of
// `'static` references, one of them returned by a function. The call leaves
// region abstractions owning the static region which hold nested shared
// borrows: they must be forgotten before joining the branches.

pub struct Loc<'a> {
    pub file: &'a str,
    pub line: u32,
}

pub fn loc() -> &'static Loc<'static> {
    &Loc {
        file: "src/lib.rs",
        line: 7,
    }
}

pub fn max_level() -> u32 {
    5
}

/// Like `log::__private_api::log`.
pub fn log_impl(arg: u32, lvl: u32, target_module_loc: &(&str, &'static str, &'static Loc<'static>)) -> u32 {
    arg + lvl + target_module_loc.2.line
}

pub fn emit(v: &mut Vec<u32>, x: u32) -> u32 {
    let lvl = 5;
    let mut r = 0;
    if lvl <= max_level() {
        r = log_impl(x, lvl, &("target", "module", loc()));
    }
    v.push(x);
    r
}

pub struct Func {
    pub x: u32,
}

/// With a nested borrow, like `Lower::emit`.
pub struct Lower<'f> {
    pub f: &'f Func,
    pub insts: Vec<u32>,
}

impl<'f> Lower<'f> {
    pub fn emit(&mut self, inst: u32) -> u32 {
        let lvl = 5;
        let mut r = 0;
        if lvl <= max_level() {
            r = log_impl(inst, lvl, &("target", "module", loc()));
        }
        self.insts.push(inst + self.f.x);
        r
    }
}

#[verify::test]
pub fn test_emit() {
    // Rust results: 3 + 5 + 7 = 15, and `v` = [3].
    let mut v = Vec::new();
    let r = emit(&mut v, 3);
    assert!(r == 15);
    assert!(v.len() == 1);
    assert!(v[0] == 3);
}

#[verify::test]
pub fn test_lower_emit() {
    // Rust results: 1 + 5 + 7 = 13, then 2 + 5 + 7 = 14, and `insts` = [11, 12].
    let f = Func { x: 10 };
    let mut l = Lower {
        f: &f,
        insts: Vec::new(),
    };
    let r1 = l.emit(1);
    let r2 = l.emit(2);
    assert!(r1 == 13);
    assert!(r2 == 14);
    assert!(l.insts.len() == 2);
    assert!(l.insts[1] == 12);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_emit() {
        super::test_emit();
    }
    #[test]
    fn test_lower_emit() {
        super::test_lower_emit();
    }
}
