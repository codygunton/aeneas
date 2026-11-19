//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] continue-on-error
// A trait method whose signature cannot be translated (here: an arrow type
// with a locally quantified region) must not abort the whole crate: the
// method and its trait are reported (and listed in `failures.json` with
// `-emit-json`), and the unrelated items below are still translated (see the
// generated `ClifvTraitMethodSigFailure.lean`).

pub trait Bad {
    fn apply(&self, g: fn(&u32) -> &u32) -> u32;
}

pub fn unrelated(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub struct Point {
    pub x: u32,
    pub y: u32,
}

pub fn swap(p: Point) -> Point {
    Point { x: p.y, y: p.x }
}
