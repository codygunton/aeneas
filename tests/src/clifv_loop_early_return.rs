//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Early returns inside loops (lowered by the `lower_loop_exits` pre-pass).
// The two loop shapes of Cranelift's `ASIMDMovModImm::maybe_from_u64`
// (cranelift/codegen/src/isa/aarch64/inst/imms.rs), with `while` loops.

pub struct ModImm {
    pub imm: u8,
    pub shift: u8,
    pub is_64bit: bool,
    pub shift_ones: bool,
}

/// "Of the 4 bytes, at most one is non-zero": the loop returns early on success.
pub fn single_byte(value: u32) -> Option<ModImm> {
    let mut shift: u32 = 0;
    while shift < 32 {
        if value & (0xFF << shift) == value {
            return Some(ModImm {
                imm: (value >> shift) as u8,
                shift: shift as u8,
                is_64bit: false,
                shift_ones: false,
            });
        }
        shift += 8;
    }
    None
}

/// "Check if all bytes are either 0 or 0xFF": the loop returns early on failure.
pub fn byte_mask(value: u64) -> Option<ModImm> {
    let mut imm = 0u8;
    let mut i: u32 = 0;
    while i < 8 {
        let b = (value >> (i * 8)) as u8;
        if b == 0 || b == 0xFF {
            imm |= (b & 1) << i;
        } else {
            return None;
        }
        i += 1;
    }
    Some(ModImm {
        imm,
        shift: 0,
        is_64bit: true,
        shift_ones: false,
    })
}

/// Whether `o` is `Some` with these fields (no `Option` equality model needed).
pub fn is(o: Option<ModImm>, imm: u8, shift: u8, is_64bit: bool, shift_ones: bool) -> bool {
    match o {
        Some(m) => {
            m.imm == imm && m.shift == shift && m.is_64bit == is_64bit && m.shift_ones == shift_ones
        }
        None => false,
    }
}

#[verify::test]
pub fn test_single_byte() {
    // Rust results: 0x4200 -> imm 0x42, shift 8; 0x4201 -> None; 0 -> imm 0, shift 0.
    assert!(is(single_byte(0x4200), 0x42, 8, false, false));
    assert!(single_byte(0x4201).is_none());
    assert!(is(single_byte(0), 0, 0, false, false));
}

#[verify::test]
pub fn test_byte_mask() {
    // Rust results: 0xFF0000FF00FF0000 -> imm 0x94; 0x0102 -> None.
    assert!(is(byte_mask(0xFF0000FF00FF0000), 0x94, 0, true, false));
    assert!(byte_mask(0x0102).is_none());
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_single_byte() {
        super::test_single_byte();
    }
    #[test]
    fn test_byte_mask() {
        super::test_byte_mask();
    }
}
