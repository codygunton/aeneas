//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] continue-on-error
#![feature(register_tool)]
#![register_tool(verify)]
// Items whose translation or extraction fails must not break the generated Lean (no `sorry`, no
// ill-formed syntax): a function is extracted as an `opaque` stub with its signature, whose
// implementation fails with `Error.undef`, so that its callers stay executable; a global or a
// trait implementation is dropped, and the functions which use it become stubs in turn. The
// failures are listed in `failures.json` with `-emit-json`.

/// The translation of the body fails (raw pointer dereference): stub.
pub fn read_via_ptr(data: &[u16; 8]) -> u16 {
    unsafe { *data.as_ptr().add(1) }
}

/// Calls the stub: a regular definition, which only fails when it reaches the stub.
pub fn caller(data: &[u16; 8], use_ptr: bool) -> u16 {
    if use_ptr { read_via_ptr(data) } else { data[1] }
}

/// The initializer fails (raw pointer dereference): the global is dropped.
pub static FAILED: u16 = unsafe { *(&5u16 as *const u16) };

/// Uses the dropped global: stub.
pub fn read_failed() -> u16 {
    FAILED
}

/// The signature of the method can not be translated (arrow type with a locally quantified
/// region): the method is dropped from the trait, and the implementation below is dropped.
pub trait Bad {
    fn apply(&self, g: fn(&u32) -> &u32) -> u32;
}

pub struct Point {
    pub x: u32,
}

impl Bad for Point {
    fn apply(&self, g: fn(&u32) -> &u32) -> u32 {
        *g(&self.x)
    }
}

pub fn generic<T: Bad>(_t: &T) -> u32 {
    0
}

/// Uses the dropped implementation: stub.
pub fn use_impl(p: &Point) -> u32 {
    generic(p)
}

fn label(x: u8) -> &'static str {
    if x == 0 { "zero" } else { "other" }
}

/// Uses the `FnOnce` implementation of a function item.
pub fn use_fn_item(o: Option<u8>) -> Option<&'static str> {
    o.map(label)
}

#[verify::test]
pub fn test_caller() {
    let data = [1, 2, 3, 4, 5, 6, 7, 8];
    // Rust result: data[1] = 2 (the stub is not reached).
    assert!(caller(&data, false) == 2);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_caller() {
        super::test_caller();
        assert!(super::caller(&[1, 2, 3, 4, 5, 6, 7, 8], true) == 2);
        assert!(super::read_failed() == 5);
        assert!(super::use_impl(&super::Point { x: 3 }) == 0);
    }
}
