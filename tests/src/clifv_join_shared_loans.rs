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

// The scrutinee of a `match` holds a borrow (in the `Some` branch only) until
// the end of the `match`: the `StorageDead` of the scrutinee is moved to the
// end of the branches so that the region abstraction of `peek` can be ended
// in both branches before joining (Cranelift's `MachBuffer::island_needed`).
pub struct Fixup {
    pub offset: u32,
    pub kind: u8,
}

impl Fixup {
    pub fn deadline(&self) -> u32 {
        self.offset.saturating_add(self.kind as u32)
    }
}

pub struct Buf {
    pub fixups: Vec<Fixup>,
    pub pending: u32,
    pub cur: u32,
}

pub fn peek(v: &Vec<Fixup>) -> Option<&Fixup> {
    v.first()
}

impl Buf {
    pub fn island_needed(&self, distance: u32) -> bool {
        let deadline = match peek(&self.fixups) {
            Some(fixup) => fixup.deadline().min(self.pending),
            None => self.pending,
        };
        deadline < u32::MAX && self.cur.saturating_add(distance) > deadline
    }
}

#[verify::test]
fn test_island_needed() {
    let b = Buf { fixups: vec![Fixup { offset: 10, kind: 2 }], pending: 100, cur: 5 };
    assert!(b.island_needed(8));
    assert!(!b.island_needed(6));
    let e = Buf { fixups: Vec::new(), pending: 100, cur: 5 };
    assert!(!e.island_needed(8));
    assert!(e.island_needed(96));
    let n = Buf { fixups: Vec::new(), pending: u32::MAX, cur: 5 };
    assert!(!n.island_needed(1000));
}
