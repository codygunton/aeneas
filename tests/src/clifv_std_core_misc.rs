//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
#![feature(register_tool)]
#![register_tool(verify)]
//! Models of `core::option`, `core::result`, `core::cmp`, `core::tuple`, ranges, iterator
//! sources and small `core` items.
//! Expected values: Rust 1.96 (`cargo test` in `tests/src`).

use core::cmp::Reverse;

#[verify::test]
pub fn test_option() {
    let a: Option<u32> = Some(3);
    let n: Option<u32> = None;
    assert!(a.unwrap_or_else(|| 7) == 3);
    assert!(n.unwrap_or_else(|| 7) == 7);
    assert!(n.unwrap_or_default() == 0);
    assert!(a.map_or(0, |x| x + 1) == 4);
    assert!(n.map_or(9, |x| x + 1) == 9);
    assert!(a.and_then(|x| if x > 2 { Some(x * 2) } else { None }) == Some(6));
    assert!(a.filter(|x| *x > 5).is_none());
    assert!(n.or(Some(5)) == Some(5));
    assert!(a.or_else(|| Some(1)) == Some(3));
    assert!(a.ok_or_else(|| 0u8).ok() == Some(3));
    assert!(!a.ok_or_else(|| 4u8).is_err());
    let mut o: Option<u32> = None;
    *o.get_or_insert(5) += 1;
    assert!(o == Some(6));
    let old = o.replace(8);
    assert!(old == Some(6) && o == Some(8));
    *o.insert(2) += 1;
    assert!(o == Some(3));
    if let Some(x) = o.as_mut() {
        *x = 11;
    }
    assert!(o.as_ref() == Some(&11));
    let r: Option<&u32> = Some(&4);
    assert!(r.copied() == Some(4) && r.cloned() == Some(4));
    assert!(true.then_some(1u8) == Some(1) && false.then_some(1u8).is_none());
}

fn first_plus_one(v: &[u32]) -> Option<u32> {
    let x = v.first()?;
    Some(*x + 1)
}

#[verify::test]
pub fn test_option_try_iter() {
    let v: [u32; 2] = [4, 5];
    assert!(first_plus_one(&v) == Some(5));
    assert!(first_plus_one(&v[..0]).is_none());
    let mut it = Some(3u32).into_iter();
    assert!(it.next() == Some(3) && it.next().is_none());
}

fn mk_ok(x: u32) -> Result<u32, u8> {
    Ok(x)
}

fn mk_err(x: u8) -> Result<u32, u8> {
    Err(x)
}

fn ok_u32(x: u32) -> Result<u32, u8> {
    Ok(x)
}

#[verify::test]
pub fn test_result() {
    let a = mk_ok(2);
    let e = mk_err(5);
    assert!(!a.is_err() && e.is_err());
    assert!(a.ok() == Some(2) && e.ok().is_none());
    assert!(e.unwrap_err() == 5);
    assert!(a.and_then(|x| if x > 1 { ok_u32(x + 1) } else { mk_err(0) }).ok() == Some(3));
    assert!(e.or_else(|x| if x > 1 { ok_u32(x as u32) } else { mk_err(x) }).ok() == Some(5));
    assert!(e.unwrap_or_else(|x| x as u32 * 2) == 10);
}

#[verify::test]
pub fn test_cmp() {
    assert!(Reverse(3u32) < Reverse(2u32));
    assert!(Reverse(3u32).cmp(&Reverse(5u32)) == core::cmp::Ordering::Greater);
    assert!(Reverse(3u32) >= Reverse(3u32));
    assert!((1u32, 2u32) < (1u32, 3u32));
    assert!((2u32, 0u32) > (1u32, 9u32));
    assert!((1u32, 2u32) <= (1u32, 2u32));
    assert!((1u32, 2u32).cmp(&(1u32, 1u32)) == core::cmp::Ordering::Greater);
    assert!((1u8, 2u8, 3u8, 4u8) < (1u8, 2u8, 4u8, 0u8));
    assert!((1u8, 2u8, 3u8, 4u8).cmp(&(1u8, 2u8, 3u8, 4u8)) == core::cmp::Ordering::Equal);
    assert!((1u8, 2u8, 3u8) != (1u8, 2u8, 4u8));
    assert!((1u8, 2u8, 3u8, 4u8) == (1u8, 2u8, 3u8, 4u8));
    assert!('a' == 'a' && 'a' != 'b');
    assert!(false < true);
    let mut v: [(u32, Reverse<u8>); 3] = [(1, Reverse(1)), (0, Reverse(2)), (1, Reverse(5))];
    v.sort_unstable_by_key(|e| (e.0, e.1));
    assert!(v[0].0 == 0 && (v[1].1).0 == 5 && (v[2].1).0 == 1);
}

#[verify::test]
pub fn test_ranges() {
    let r = 2u32..7u32;
    assert!(r.clone().count() == 5);
    assert!(r.clone().last() == Some(6));
    assert!(r.clone().max() == Some(6));
    let mut r2 = r.clone();
    assert!(r2.nth(2) == Some(4));
    assert!(r2.next() == Some(5));
    assert!(r2.nth(5).is_none());
    assert!(r2.next().is_none());
    let (lo, hi) = r.size_hint();
    assert!(lo == 5 && hi == Some(5));
    let mut f = 10usize..;
    assert!(f.next() == Some(10) && f.next() == Some(11));
}

#[verify::test]
pub fn test_sources() {
    let mut e = core::iter::empty::<u32>();
    assert!(e.next().is_none());
    let mut o = core::iter::once(4u32);
    assert!(o.next() == Some(4) && o.next().is_none());
    let mut r = core::iter::repeat(3u8);
    assert!(r.next() == Some(3) && r.nth(10) == Some(3));
    let a: [u32; 3] = [5, 6, 7];
    let mut it = a.into_iter();
    assert!(it.next() == Some(5));
    assert!(it.fold(0u32, |s, x| s + x) == 13);
    assert!(a.into_iter().count() == 3);
    assert!(a.into_iter().last() == Some(7));
    let (lo, hi) = a.into_iter().size_hint();
    assert!(lo == 3 && hi == Some(3));
}

#[verify::test]
pub fn test_misc() {
    let mut v: u32 = 5;
    let old = core::mem::take(&mut v);
    assert!(old == 5 && v == 0);
    assert!(core::mem::size_of::<u64>() == 8);
    let x: usize = 0b1011;
    assert!(x & 3 == 3 && x | 4 == 15 && !0u16 == 0xFFFF && (1u8 << 3u8) == 8 && (x >> 1u8) == 5);
    assert!(3u32 + 4u32 == 7 && 9u16 - 4u16 == 5);
}

#[cfg(test)]
mod tests {
    #[test]
    fn all() {
        super::test_option();
        super::test_option_try_iter();
        super::test_result();
        super::test_cmp();
        super::test_ranges();
        super::test_sources();
        super::test_misc();
    }
}
