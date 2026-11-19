//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Models of `alloc::string`, `alloc::str`, `alloc::fmt` and `alloc::borrow` items.
use std::borrow::Cow;
use std::fmt::Write;

#[verify::test]
pub fn test_string_ops() {
    let mut s = String::new();
    s.push_str("ab");
    s.push('é');
    assert!(s.len() == 4);
    let t = s.clone();
    assert!(t == s);
    let mut u = String::with_capacity(8);
    u.push_str("abé");
    assert!(u == s);
    let v = String::from("xyz");
    assert!(v.len() == 3);
    let w: String = "xyz".to_owned();
    assert!(w == v);
    let r: &str = &v[1..];
    assert!(r.len() == 2);
    let mut x = String::new();
    let _ = x.write_str("hi");
    let _ = x.write_char('!');
    assert!(x.len() == 3);
}

#[verify::test]
pub fn test_join() {
    let parts: [&str; 3] = ["a", "bc", "d"];
    let j = parts.join(", ");
    assert!(j.len() == 8);
    assert!(j == "a, bc, d");
}

#[verify::test]
pub fn test_replace() {
    let s = "0x1_00_0".replace("_", "");
    assert!(s == "0x1000");
    let t = "aaa".replace("aa", "b");
    assert!(t == "ba");
}

#[verify::test]
pub fn test_format() {
    let n: u32 = 42;
    let s = format!("n={} {}", n, "x");
    assert!(s == "n=42 x");
    let t = n.to_string();
    assert!(t == "42");
    let st = String::from("q");
    let d = format!("[{}|{:>3}|{:?}]", st, st, st);
    assert!(d == "[q|  q|\"q\"]");
    let c: Cow<str> = Cow::Borrowed("cow");
    let e = format!("{}", c);
    assert!(e == "cow");
}

#[cfg(test)]
mod tests {
    #[test]
    fn all() {
        super::test_string_ops();
        super::test_join();
        super::test_replace();
        super::test_format();
    }
}
