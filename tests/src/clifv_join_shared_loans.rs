//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Loops reading through a shared borrow of a struct which itself contains
// shared borrows (`&Tmpl<'a>` with `Tmpl<'a> { names: &'a [..] }`), in the
// shape of Cranelift's `constant_hash::probe` (open addressing with quadratic
// probing over a settings template). The loop entry contexts contain region
// abstractions whose shared loans have shared values containing shared
// borrows: joining them used to be rejected.

pub struct Tmpl<'a> {
    pub names: &'a [u32],
}

impl<'a> Tmpl<'a> {
    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn key(&self, idx: usize) -> Option<u32> {
        let k = self.names[idx];
        if k == 0 { None } else { Some(k) }
    }
}

/// Returns `Ok(idx)` with the index of `key`, or `Err(idx)` with the index of
/// the empty slot ending the probe sequence.
pub fn probe(table: &Tmpl, key: u32, hash: usize) -> Result<usize, usize> {
    let mask = table.len() - 1;
    let mut idx = hash;
    let mut step = 0;
    loop {
        idx &= mask;
        match table.key(idx) {
            None => return Err(idx),
            Some(k) if k == key => return Ok(idx),
            _ => {}
        }
        step += 1;
        idx += step;
    }
}

/// Counts the entries of the table, iterating with a `while` loop.
pub fn count(table: &Tmpl) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < table.len() {
        if table.key(i).is_some() {
            n += 1;
        }
        i += 1;
    }
    n
}

#[verify::test]
fn test_probe() {
    let names: [u32; 8] = [1, 9, 0, 3, 4, 0, 5, 0];
    let t = Tmpl { names: &names };
    assert!(matches!(probe(&t, 3, 3), Ok(3)));
    assert!(matches!(probe(&t, 5, 3), Ok(6)));
    assert!(matches!(probe(&t, 7, 3), Err(5)));
    assert!(matches!(probe(&t, 9, 9), Ok(1)));
    assert!(matches!(probe(&t, 8, 2), Err(2)));
    assert!(count(&t) == 5);
}
