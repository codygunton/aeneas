//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Static borrows hidden in ADTs (`Cow<'static, str>`, `&'static [u8]`), read
// through shared borrows in matches and loops, in the shape of Cranelift's
// `VCodeConstantData` (`MachBuffer::register_constants`), `AliasRegionData`
// (`Verifier::verify_alias_regions`) and the many loops iterating over the
// entities of an `ir::Function`:
// - matching a shared borrow of an enum with a `&'static [u8]` field (the
//   shared value is reborrowed before the match: the static loans of the
//   reborrowed copy must be tracked);
// - loops over slices of structs containing static borrows (the shared values
//   in the joined region abstractions contain shared borrows, the static loans
//   of the dropped loop elements must be eliminated during the collapse, and
//   the abstractions of the static region must be consistent across joins).
use std::borrow::Cow;

pub enum ConstData {
    Pool(Vec<u8>),
    WellKnown(&'static [u8]),
    U64(u64),
}

impl ConstData {
    pub fn len(&self) -> usize {
        match self {
            ConstData::Pool(v) => v.len(),
            ConstData::WellKnown(s) => s.len(),
            ConstData::U64(_) => 8,
        }
    }
}

pub struct Consts {
    pub v: Vec<ConstData>,
}

pub struct Buf {
    pub n: Vec<usize>,
}

impl Buf {
    fn register_constant(&mut self, c: &usize, d: &ConstData) {
        self.n.push(*c + d.len());
    }

    pub fn register_constants(&mut self, cs: &Consts) {
        for i in 0..cs.v.len() {
            let val = &cs.v[i];
            self.register_constant(&i, val);
        }
    }
}

pub struct AliasRegionData {
    pub user_id: u32,
    pub description: Cow<'static, str>,
}

pub struct Named {
    pub id: u32,
    pub name: &'static str,
}

pub struct Func {
    pub alias_regions: Vec<AliasRegionData>,
    pub named: Vec<Named>,
}

pub struct Verifier<'a> {
    pub func: &'a Func,
}

impl<'a> Verifier<'a> {
    /// Returns the (index, user id) pairs of the duplicated user ids.
    pub fn verify_alias_regions(&self, errors: &mut Vec<(usize, u32)>) {
        let mut seen: Vec<u32> = Vec::new();
        for (ar, ar_data) in self.func.alias_regions.iter().enumerate() {
            if seen.contains(&ar_data.user_id) {
                errors.push((ar, ar_data.user_id));
            } else {
                seen.push(ar_data.user_id);
            }
        }
    }

    /// Returns the id of the last named entity (or 0).
    pub fn last_id(&self) -> u32 {
        let mut s = 0;
        for n in self.func.named.iter() {
            s = n.id;
        }
        s
    }
}

fn region(user_id: u32) -> AliasRegionData {
    AliasRegionData {
        user_id,
        description: Cow::Owned(String::new()),
    }
}

#[verify::test]
fn test_register_constants() {
    // Rust results: the index plus the length of each constant.
    let mut v = Vec::new();
    v.push(ConstData::U64(0));
    v.push(ConstData::Pool(vec![1, 2]));
    v.push(ConstData::Pool(Vec::new()));
    let cs = Consts { v };
    let mut b = Buf { n: Vec::new() };
    b.register_constants(&cs);
    assert!(b.n.len() == 3);
    assert!(b.n[0] == 8);
    assert!(b.n[1] == 3);
    assert!(b.n[2] == 2);
}

#[verify::test]
fn test_verify_alias_regions() {
    // Rust results: the user ids 3 and 1 are duplicated at indices 2 and 3.
    let mut alias_regions = Vec::new();
    alias_regions.push(region(1));
    alias_regions.push(region(3));
    alias_regions.push(region(3));
    alias_regions.push(region(1));
    alias_regions.push(region(2));
    let f = Func {
        alias_regions,
        named: Vec::new(),
    };
    let v = Verifier { func: &f };
    let mut errors = Vec::new();
    v.verify_alias_regions(&mut errors);
    assert!(errors.len() == 2);
    assert!(errors[0].0 == 2 && errors[0].1 == 3);
    assert!(errors[1].0 == 3 && errors[1].1 == 1);
    assert!(v.last_id() == 0);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_register_constants() {
        super::test_register_constants();
    }
    #[test]
    fn test_verify_alias_regions() {
        super::test_verify_alias_regions();
    }
}
