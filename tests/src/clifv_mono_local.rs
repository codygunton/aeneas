//@ [!lean] skip
//@ charon-args=--monomorphize
#![feature(register_tool)]
#![register_tool(verify)]
// Monomorphized LLBC (`charon --preset=aeneas --monomorphize`) of local items
// only (no standard library calls): every generic function, type, trait method
// and default method is instantiated per use and named with its instantiation
// (the `PeInstantiated` name suffix).

pub enum Opt<T> {
    No,
    Yes(T),
}

pub struct Pair<T> {
    pub a: T,
    pub b: T,
}

pub trait Shape {
    fn area(&self) -> u32;
    fn scaled(&self, k: u32) -> u32 {
        self.area() * k
    }
}

pub struct Square {
    pub side: u32,
}

pub struct Rect {
    pub w: u32,
    pub h: u32,
}

impl Shape for Square {
    fn area(&self) -> u32 {
        self.side * self.side
    }
}

impl Shape for Rect {
    fn area(&self) -> u32 {
        self.w * self.h
    }
    fn scaled(&self, k: u32) -> u32 {
        self.w * self.h * k + 1
    }
}

/// Uses the default `scaled`, like `Square`: two instances of the default
/// method must get distinct names.
pub struct Three;

impl Shape for Three {
    fn area(&self) -> u32 {
        3
    }
}

pub fn id<T>(x: T) -> T {
    x
}

pub fn swap<T>(p: Pair<T>) -> Pair<T> {
    Pair { a: p.b, b: p.a }
}

pub fn first<T>(p: Pair<T>) -> T {
    p.a
}

pub fn get_or<T>(o: Opt<T>, d: T) -> T {
    match o {
        Opt::Yes(x) => x,
        Opt::No => d,
    }
}

pub fn sum_areas<S: Shape>(a: &S, b: &S) -> u32 {
    a.area() + b.area()
}

pub fn double_scaled<S: Shape>(s: &S) -> u32 {
    s.scaled(2)
}

#[verify::test]
pub fn test_generic_fns() {
    // Rust results: 7, true, 2, 4, 9, 5, false.
    assert!(id(7u32) == 7);
    assert!(id(true));
    assert!(swap(Pair { a: 1u64, b: 2u64 }).a == 2);
    assert!(first(swap(Pair { a: Square { side: 3 }, b: Square { side: 4 } })).side == 4);
    assert!(get_or(Opt::Yes(9u8), 5) == 9);
    assert!(get_or(Opt::No, 5u8) == 5);
    assert!(!get_or(Opt::No, false));
}

#[verify::test]
pub fn test_traits() {
    // Rust results: 9 + 4 = 13; 6 + 2 = 8; 2 * 9 = 18; 2 * 3 * 2 + 1 = 13;
    // 2 * 3 = 6.
    assert!(sum_areas(&Square { side: 3 }, &Square { side: 2 }) == 13);
    assert!(sum_areas(&Rect { w: 2, h: 3 }, &Rect { w: 1, h: 2 }) == 8);
    assert!(double_scaled(&Square { side: 3 }) == 18);
    assert!(double_scaled(&Rect { w: 2, h: 3 }) == 13);
    assert!(double_scaled(&Three) == 6);
}

#[cfg(test)]
mod tests {
    #[test]
    fn run() {
        super::test_generic_fns();
        super::test_traits();
    }
}
