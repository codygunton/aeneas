//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Cranelift's `ASIMDMovModImm::maybe_from_u64`
// (cranelift/codegen/src/isa/aarch64/inst/imms.rs), verbatim: early returns
// inside `for` loops over ranges, after a match whose other branches return.

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ScalarSize {
    Size8,
    Size16,
    Size32,
    Size64,
    Size128,
}

#[derive(Clone, Copy)]
pub struct ASIMDMovModImm {
    imm: u8,
    shift: u8,
    is_64bit: bool,
    shift_ones: bool,
}

impl ASIMDMovModImm {
    /// Construct an ASIMDMovModImm from an arbitrary 64-bit constant, if possible.
    /// Note that the bits in `value` outside of the range specified by `size` are
    /// ignored; for example, in the case of `ScalarSize::Size8` all bits above the
    /// lowest 8 are ignored.
    pub fn maybe_from_u64(value: u64, size: ScalarSize) -> Option<ASIMDMovModImm> {
        match size {
            ScalarSize::Size8 => Some(ASIMDMovModImm {
                imm: value as u8,
                shift: 0,
                is_64bit: false,
                shift_ones: false,
            }),
            ScalarSize::Size16 => {
                let value = value as u16;

                if value >> 8 == 0 {
                    Some(ASIMDMovModImm {
                        imm: value as u8,
                        shift: 0,
                        is_64bit: false,
                        shift_ones: false,
                    })
                } else if value as u8 == 0 {
                    Some(ASIMDMovModImm {
                        imm: (value >> 8) as u8,
                        shift: 8,
                        is_64bit: false,
                        shift_ones: false,
                    })
                } else {
                    None
                }
            }
            ScalarSize::Size32 => {
                let value = value as u32;

                // Value is of the form 0x00MMFFFF.
                if value & 0xFF00FFFF == 0x0000FFFF {
                    let imm = (value >> 16) as u8;

                    Some(ASIMDMovModImm {
                        imm,
                        shift: 16,
                        is_64bit: false,
                        shift_ones: true,
                    })
                // Value is of the form 0x0000MMFF.
                } else if value & 0xFFFF00FF == 0x000000FF {
                    let imm = (value >> 8) as u8;

                    Some(ASIMDMovModImm {
                        imm,
                        shift: 8,
                        is_64bit: false,
                        shift_ones: true,
                    })
                } else {
                    // Of the 4 bytes, at most one is non-zero.
                    for shift in (0..32).step_by(8) {
                        if value & (0xFF << shift) == value {
                            return Some(ASIMDMovModImm {
                                imm: (value >> shift) as u8,
                                shift,
                                is_64bit: false,
                                shift_ones: false,
                            });
                        }
                    }

                    None
                }
            }
            ScalarSize::Size64 => {
                let mut imm = 0u8;

                // Check if all bytes are either 0 or 0xFF.
                for i in 0..8 {
                    let b = (value >> (i * 8)) as u8;

                    if b == 0 || b == 0xFF {
                        imm |= (b & 1) << i;
                    } else {
                        return None;
                    }
                }

                Some(ASIMDMovModImm {
                    imm,
                    shift: 0,
                    is_64bit: true,
                    shift_ones: false,
                })
            }
            _ => None,
        }
    }
}

pub fn is(o: Option<ASIMDMovModImm>, imm: u8, shift: u8, is_64bit: bool, shift_ones: bool) -> bool {
    match o {
        Some(m) => {
            m.imm == imm && m.shift == shift && m.is_64bit == is_64bit && m.shift_ones == shift_ones
        }
        None => false,
    }
}

#[verify::test]
pub fn test_maybe_from_u64() {
    assert!(is(ASIMDMovModImm::maybe_from_u64(0xFF0000FF00FF0000, ScalarSize::Size64), 0x94, 0, true, false));
    assert!(is(ASIMDMovModImm::maybe_from_u64(4390911, ScalarSize::Size32), 66, 16, false, true));
    assert!(ASIMDMovModImm::maybe_from_u64(513, ScalarSize::Size16).is_none());
    assert!(is(ASIMDMovModImm::maybe_from_u64(0x00450000, ScalarSize::Size32), 0x45, 16, false, false));
    assert!(ASIMDMovModImm::maybe_from_u64(0x00450001, ScalarSize::Size32).is_none());
    assert!(ASIMDMovModImm::maybe_from_u64(0x00000000_000012FF, ScalarSize::Size64).is_none());
    assert!(is(ASIMDMovModImm::maybe_from_u64(0x1234, ScalarSize::Size8), 0x34, 0, false, false));
    assert!(ASIMDMovModImm::maybe_from_u64(1, ScalarSize::Size128).is_none());
}
