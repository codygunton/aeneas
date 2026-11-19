//@ [!lean] skip
//@ charon-args=--code-duplication-limit 2
#![feature(register_tool)]
#![register_tool(verify)]
// Cranelift's `enc_acq_rel` (cranelift/codegen/src/isa/aarch64/inst/emit.rs):
// locals defined by matches (`let sz = match ty {..}`), whose branchings the
// join pre-passes rewrite with flags (`init_join_scalars`). With
// `--code-duplication-limit 2`, as in the Cranelift extraction.

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Type(u16);
pub const I8: Type = Type(0x74);
pub const I16: Type = Type(0x75);
pub const I32: Type = Type(0x76);
pub const I64: Type = Type(0x77);

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AtomicRMWOp {
    Add,
    Clr,
    Eor,
    Set,
    Smax,
    Smin,
    Umax,
    Umin,
    Swp,
}

fn gpr(r: u32) -> u32 {
    r & 31
}

pub fn enc_acq_rel(ty: Type, op: AtomicRMWOp, rs: u32, rt: u32, rn: u32) -> u32 {
    assert!(gpr(rt) != 31);
    let sz = match ty {
        I64 => 0b11,
        I32 => 0b10,
        I16 => 0b01,
        I8 => 0b00,
        _ => unreachable!(),
    };
    let bit15 = match op {
        AtomicRMWOp::Swp => 0b1,
        _ => 0b0,
    };
    let op = match op {
        AtomicRMWOp::Add => 0b000,
        AtomicRMWOp::Clr => 0b001,
        AtomicRMWOp::Eor => 0b010,
        AtomicRMWOp::Set => 0b011,
        AtomicRMWOp::Smax => 0b100,
        AtomicRMWOp::Smin => 0b101,
        AtomicRMWOp::Umax => 0b110,
        AtomicRMWOp::Umin => 0b111,
        AtomicRMWOp::Swp => 0b000,
    };
    0b00_111_000_111_00000_0_000_00_00000_00000
        | (sz << 30)
        | (gpr(rs) << 16)
        | bit15 << 15
        | (op << 12)
        | (gpr(rn) << 5)
        | gpr(rt)
}

#[verify::test]
pub fn test_enc_acq_rel() {
    assert!(enc_acq_rel(I64, AtomicRMWOp::Swp, 1, 2, 3) == 0xf8e18062);
    assert!(enc_acq_rel(I32, AtomicRMWOp::Add, 4, 5, 6) == 0xb8e400c5);
    assert!(enc_acq_rel(I8, AtomicRMWOp::Umin, 7, 8, 9) == 0x38e77128);
}
