//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Values bound from a conditional whose type Lean can't infer from the first branch it
// elaborates: a branch returning a comparison (`MachBuffer::handle_fixup`'s
// `veneer_required`) makes `ok (x > y)` a `Prop`, and a polymorphic constructor (the
// `return None` of `ImmLogic::maybe_from_u64`) leaves metavariables. The conditional is
// ascribed its type.

pub fn veneer_required(offset: u32, label: u32, max_pos: u32, max_neg: u32) -> u32 {
    let required = if label >= offset {
        assert!(label - offset <= max_pos);
        false
    } else {
        offset - label > max_neg
    };
    if required { 1 } else { 0 }
}

pub fn maybe_half(value: u64, is_32: bool, is_16: bool) -> Option<u64> {
    if is_32 {
        if is_16 {
            return None;
        }
    }
    let mut v = value;
    let mut i = 0;
    while i < 3 {
        if v & 1 == 1 {
            return Some(i);
        }
        v >>= 1;
        i += 1;
    }
    Some(value / 2)
}

#[verify::test]
pub fn test_veneer_required() {
    assert!(veneer_required(10, 12, 4, 4) == 0);
    assert!(veneer_required(10, 2, 4, 4) == 1);
    assert!(veneer_required(10, 8, 4, 4) == 0);
    assert!(maybe_half(8, true, true).is_none());
    assert!(maybe_half(8, true, false) == Some(4));
    assert!(maybe_half(2, false, false) == Some(1));
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_veneer_required() {
        super::test_veneer_required();
    }
}
