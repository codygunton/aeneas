//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// String literals are printed with Lean's escapes: non-ASCII characters are kept as UTF-8 (OCaml
// would print the decimal escapes `\194\171`) and a single quote is not escaped (Cranelift's
// parser messages `expected constant number: const«n»` and `expected ')' to end sarg size`).

pub fn message(i: u32) -> &'static str {
    match i {
        0 => "expected constant number: const«n»",
        1 => "expected ')' to end sarg size",
        2 => "tab\tquote\"backslash\\newline\n",
        _ => "",
    }
}

#[verify::test]
pub fn test_message() {
    assert!(message(0).len() == 36);
    assert!(message(1).len() == 29);
    assert!(message(2).len() == 28);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_message() {
        super::test_message();
    }
}
