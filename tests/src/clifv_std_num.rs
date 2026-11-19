//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Models of `core::num` (integer methods, parsing, `NonZero`) and `core::convert::num`.
// The expected values were obtained by running this file natively (rustc 1.96).
use core::num::NonZeroU64;

fn opt_is<T: PartialEq>(o: Option<T>, v: T) -> bool {
    match o {
        Some(x) => x == v,
        None => false,
    }
}
fn is_nothing<T>(o: Option<T>) -> bool {
    match o {
        Some(_) => false,
        None => true,
    }
}
fn ok_is<T: PartialEq, E>(r: Result<T, E>, v: T) -> bool {
    match r {
        Ok(x) => x == v,
        Err(_) => false,
    }
}
fn is_error<T, E>(r: Result<T, E>) -> bool {
    match r {
        Ok(_) => false,
        Err(_) => true,
    }
}

pub fn wdiv_i8(a: i8, b: i8) -> i8 {
    a.wrapping_div(b)
}

#[verify::test]
fn test_int_methods() {
    assert!(wdiv_i8(-128, -1) == -128);
    assert!(7u32.wrapping_div(2) == 3);
    assert!(opt_is(1u8.checked_shl(7), 128));
    assert!(is_nothing(1u8.checked_shl(8)));
    assert!(opt_is((-8i32).checked_shr(1), -4));
    assert!(is_nothing(0u32.checked_ilog2()));
    assert!(opt_is(1000u64.checked_ilog2(), 9));
    assert!(is_nothing((-5i32).checked_ilog2()));
    assert!(1024usize.ilog2() == 10);
    assert!(0u16.trailing_zeros() == 16);
    assert!(8u64.trailing_zeros() == 3);
    assert!(0i8.trailing_zeros() == 8);
    assert!(0b0111u8.trailing_ones() == 3);
    assert!(0xF0u8.leading_ones() == 4);
    assert!((-1i32).leading_ones() == 32);
    assert!(0xFFu64.count_ones() == 8);
    assert!(5usize.count_ones() == 2);
    assert!(is_nothing(i32::MIN.checked_neg()));
    assert!(opt_is(5i64.checked_neg(), -5));
    assert!(1u32.wrapping_neg() == u32::MAX);
    assert!(i128::MIN.wrapping_neg() == i128::MIN);
    assert!((-5i64).abs() == 5);
    assert!(3000000000u32.saturating_mul(2) == u32::MAX);
}

#[verify::test]
fn test_parse() {
    assert!(ok_is("123".parse::<u8>(), 123));
    assert!(is_error("256".parse::<u8>()));
    assert!(is_error("-1".parse::<u8>()));
    assert!(ok_is("-32768".parse::<i16>(), -32768));
    assert!(is_error("+".parse::<u32>()));
    assert!(is_error("".parse::<u16>()));
    assert!(ok_is(u32::from_str_radix("ff", 16), 255));
    assert!(ok_is(u128::from_str_radix("zz", 36), 1295));
}

fn nz_trailing_zeros(x: u64) -> u32 {
    match NonZeroU64::new(x) {
        Some(n) => n.trailing_zeros(),
        None => 99,
    }
}
fn nz_get(x: u64) -> u64 {
    match NonZeroU64::new(x) {
        Some(n) => n.get(),
        None => 0,
    }
}

#[verify::test]
fn test_nonzero() {
    assert!(is_nothing(NonZeroU64::new(0)));
    assert!(nz_trailing_zeros(8) == 3);
    assert!(nz_get(8) == 8);
    #[allow(deprecated)]
    let m = core::usize::MAX;
    assert!(m == usize::MAX);
}

#[verify::test]
fn test_convert() {
    assert!(i16::from(200u8) == 200);
    assert!(i64::from(u32::MAX) == 4294967295);
    assert!(is_error(u8::try_from(300u16)));
    assert!(ok_is(u8::try_from(255u32), 255));
    assert!(is_error(i8::try_from(-129i32)));
    assert!(ok_is(i8::try_from(-128i64), -128));
    assert!(is_error(usize::try_from(-1isize)));
    assert!(is_error(u16::try_from(70000usize)));
    assert!(ok_is(usize::try_from(5u64), 5));
    assert!(is_error(u32::try_from(-1i8)));
}
