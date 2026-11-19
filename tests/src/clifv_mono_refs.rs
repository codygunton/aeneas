//@ [!lean] skip
//@ charon-args=--monomorphize-local-only
#![feature(register_tool)]
#![register_tool(verify)]
// Local-only monomorphized LLBC (`charon --preset=aeneas
// --monomorphize-local-only`): local generic items instantiated with
// references keep one region parameter per region of their instantiation
// (e.g. `Holder::<&'a u32><'a>`), so borrows still flow through them.

pub struct Holder<T> {
    pub x: T,
}

pub fn mk<T>(x: T) -> Holder<T> {
    Holder { x }
}

pub fn get<T: Copy>(h: &Holder<T>) -> T {
    h.x
}

pub fn read_through(a: &u32) -> u32 {
    let h = mk(a);
    *get(&h)
}

pub fn incr_through(a: &mut u32) {
    let h = mk(a);
    *h.x += 1;
}

pub fn incr_twice(mut v: u32) -> u32 {
    incr_through(&mut v);
    incr_through(&mut v);
    v
}

#[verify::test]
pub fn test_refs() {
    // Rust results: 7, 5.
    let a: u32 = 7;
    assert!(read_through(&a) == 7);
    assert!(incr_twice(3) == 5);
}

#[cfg(test)]
mod tests {
    #[test]
    fn run() {
        super::test_refs();
    }
}
