//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// `f32`/`f64` support: literals, arithmetic, comparisons, casts, `to_bits`/`from_bits`.
// The expected values were obtained by running this file natively (rustc 1.96, x86-64).

pub fn add32(a: f32, b: f32) -> f32 {
    a + b
}
pub fn sub32(a: f32, b: f32) -> f32 {
    a - b
}
pub fn mul32(a: f32, b: f32) -> f32 {
    a * b
}
pub fn div32(a: f32, b: f32) -> f32 {
    a / b
}
pub fn rem32(a: f32, b: f32) -> f32 {
    a % b
}
pub fn neg32(a: f32) -> f32 {
    -a
}
pub fn add64(a: f64, b: f64) -> f64 {
    a + b
}
pub fn rem64(a: f64, b: f64) -> f64 {
    a % b
}

pub fn eq32(a: f32, b: f32) -> bool {
    a == b
}
pub fn ne32(a: f32, b: f32) -> bool {
    a != b
}
pub fn lt32(a: f32, b: f32) -> bool {
    a < b
}
pub fn ge64(a: f64, b: f64) -> bool {
    a >= b
}

pub fn f32_to_u32(x: f32) -> u32 {
    x as u32
}
pub fn f32_to_u8(x: f32) -> u8 {
    x as u8
}
pub fn f32_to_i32(x: f32) -> i32 {
    x as i32
}
pub fn f64_to_i64(x: f64) -> i64 {
    x as i64
}
pub fn f64_to_u64(x: f64) -> u64 {
    x as u64
}
pub fn u32_to_f32(x: u32) -> f32 {
    x as f32
}
pub fn u64_to_f32(x: u64) -> f32 {
    x as f32
}
pub fn i64_to_f64(x: i64) -> f64 {
    x as f64
}
pub fn i32_to_f32(x: i32) -> f32 {
    x as f32
}
pub fn u128_to_f32(x: u128) -> f32 {
    x as f32
}
pub fn f32_to_f64(x: f32) -> f64 {
    x as f64
}
pub fn f64_to_f32(x: f64) -> f32 {
    x as f32
}

/// The shape of regalloc2's `spill_weight_from_constraint`.
pub fn hot_bonus(loop_depth: usize) -> f32 {
    let mut b: f32 = 1000.0;
    let mut i = 0;
    while i < loop_depth {
        b = b * 4.0;
        i += 1;
    }
    b
}

pub fn cmp_is_none(a: f32, b: f32) -> bool {
    a.partial_cmp(&b).is_none()
}

#[verify::test]
fn test_float_arith() {
    assert!(add32(0.1, 0.2).to_bits() == 0x3E99999A);
    assert!(add64(0.1, 0.2).to_bits() == 0x3FD3333333333334);
    assert!(sub32(1.0, 0.9).to_bits() == 0x3DCCCCD0);
    assert!(mul32(0.1, 3.0).to_bits() == 0x3E99999A);
    assert!(div32(1.0, 3.0).to_bits() == 0x3EAAAAAB);
    assert!(div32(1.0, 0.0).to_bits() == 0x7F800000);
    assert!(neg32(0.0).to_bits() == 0x80000000);
    assert!(rem32(5.5, 2.0).to_bits() == 0x3FC00000);
    assert!(rem32(-5.5, 2.0).to_bits() == 0xBFC00000);
    assert!(rem64(1.0e300, 3.0).to_bits() == 0);
    assert!(hot_bonus(3).to_bits() == 0x477A0000);
}

#[verify::test]
fn test_float_cmp() {
    let nan = f32::from_bits(0x7FC00000);
    assert!(!eq32(nan, nan));
    assert!(ne32(nan, nan));
    assert!(eq32(0.0, -0.0));
    assert!(lt32(-1.0, 0.5));
    assert!(!lt32(nan, 1.0));
    assert!(ge64(2.0, 2.0));
    assert!(cmp_is_none(nan, 1.0));
    assert!(!cmp_is_none(1.0, 2.0));
}

#[verify::test]
fn test_float_casts() {
    let nan = f32::from_bits(0x7FC00000);
    let inf = f32::from_bits(0x7F800000);
    assert!(f32_to_u32(nan) == 0);
    assert!(f32_to_u8(inf) == 255);
    assert!(f32_to_u8(300.5) == 255);
    assert!(f32_to_u32(-1.5) == 0);
    assert!(f32_to_i32(-3.99) == -3);
    assert!(f32_to_i32(3.99) == 3);
    assert!(f32_to_i32(1.0e10) == i32::MAX);
    assert!(f32_to_i32(-1.0e10) == i32::MIN);
    assert!(f64_to_i64(-9.3e18) == i64::MIN);
    assert!(f64_to_u64(1.8446744073709552e19) == u64::MAX);
    assert!(f64_to_u64(4.5e15) == 4500000000000000);
    assert!(u32_to_f32(16777217).to_bits() == 0x4B800000);
    assert!(u32_to_f32(16777219).to_bits() == 0x4B800002);
    assert!(u64_to_f32(u64::MAX).to_bits() == 0x5F800000);
    assert!(i32_to_f32(-7).to_bits() == 0xC0E00000);
    assert!(i64_to_f64(-9007199254740993).to_bits() == 0xC340000000000000);
    assert!(u128_to_f32(u128::MAX).to_bits() == 0x7F800000);
    assert!(f32_to_f64(0.1).to_bits() == 0x3FB99999A0000000);
    assert!(f64_to_f32(0.1).to_bits() == 0x3DCCCCCD);
    assert!(f64_to_f32(1.0e40).to_bits() == 0x7F800000);
    assert!(f32::from_bits(0x7FA00001).to_bits() == 0x7FA00001);
    assert!(f64::from_bits(1).to_bits() == 1);
}
