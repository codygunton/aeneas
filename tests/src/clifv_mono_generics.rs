//@ [!lean] skip
//@ charon-args=--monomorphize-local-only
#![feature(register_tool)]
#![register_tool(verify)]
// Local-only monomorphized LLBC (`charon --preset=aeneas
// --monomorphize-local-only`): local generic functions, generic types, traits
// and default methods are instantiated per use, and called through the
// polymorphic standard library (`Vec`, slices, `Option`).

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
}

pub fn total<S: Shape>(shapes: &[S]) -> u32 {
    let mut acc = 0;
    let mut i = 0;
    while i < shapes.len() {
        acc += shapes[i].area();
        i += 1;
    }
    acc
}

pub fn double_scaled<S: Shape>(s: &S) -> u32 {
    s.scaled(2)
}

pub struct Pair<T> {
    pub a: T,
    pub b: T,
}

pub fn swap<T>(p: Pair<T>) -> Pair<T> {
    Pair { a: p.b, b: p.a }
}

pub fn id<T>(x: T) -> T {
    x
}

pub fn use_id(x: u32, y: bool) -> u32 {
    if id(y) { id(x) } else { 0 }
}

pub fn swap_u32(a: u32, b: u32) -> u32 {
    let p = swap(Pair { a, b });
    p.a
}

pub fn swap_square(a: Square, b: Square) -> u32 {
    let p = swap(Pair { a, b });
    p.a.area()
}

pub struct Stack<T> {
    pub items: Vec<T>,
}

impl<T: Copy> Stack<T> {
    pub fn new() -> Self {
        Stack { items: Vec::new() }
    }

    pub fn push(&mut self, x: T) {
        self.items.push(x)
    }

    pub fn top(&self) -> Option<T> {
        let n = self.items.len();
        if n == 0 { None } else { Some(self.items[n - 1]) }
    }
}

pub fn stack_top(a: u64, b: u64) -> u64 {
    let mut s: Stack<u64> = Stack::new();
    s.push(a);
    s.push(b);
    match s.top() {
        Some(x) => x,
        None => 0,
    }
}

pub fn stack_top_bool(a: bool) -> bool {
    let mut s: Stack<bool> = Stack::new();
    s.push(a);
    match s.top() {
        Some(x) => x,
        None => false,
    }
}

/// Instantiated with closures from two different functions: the closure
/// types are both `{closure}`, so the instance names must keep the function
/// each closure comes from (`Wrap<add_one::{closure}>` vs
/// `Wrap<times_two::{closure}>`).
pub struct Wrap<F> {
    pub f: F,
}

impl<F: Fn(u32) -> u32> Wrap<F> {
    pub fn call(&self, x: u32) -> u32 {
        (self.f)(x)
    }
}

pub fn add_one(x: u32) -> u32 {
    let w = Wrap { f: |y: u32| y + 1 };
    w.call(x)
}

pub fn times_two(x: u32) -> u32 {
    let w = Wrap { f: |y: u32| y * 2 };
    w.call(x)
}

#[verify::test]
pub fn test_traits() {
    // Rust results: 9 + 4 = 13; 2 * 6 = 12; 2 * 3 * 3 = 18.
    let sq: [Square; 2] = [Square { side: 3 }, Square { side: 2 }];
    assert!(total(&sq) == 13);
    let r: [Rect; 1] = [Rect { w: 2, h: 3 }];
    assert!(total(&r) == 6);
    assert!(double_scaled(&Rect { w: 2, h: 3 }) == 12);
    assert!(double_scaled(&Square { side: 3 }) == 18);
}

#[verify::test]
pub fn test_generics() {
    // Rust results: 7, 0, 2, 16, 5, true, 6, 10.
    assert!(use_id(7, true) == 7);
    assert!(use_id(7, false) == 0);
    assert!(swap_u32(1, 2) == 2);
    assert!(swap_square(Square { side: 3 }, Square { side: 4 }) == 16);
    assert!(stack_top(4, 5) == 5);
    assert!(stack_top_bool(true));
    assert!(add_one(5) == 6);
    assert!(times_two(5) == 10);
}

#[cfg(test)]
mod tests {
    #[test]
    fn run() {
        super::test_traits();
        super::test_generics();
    }
}
