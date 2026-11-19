//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// A deeply nested conditional (Cranelift's `FromStr` implementations: a `match` on a string with
// many arms): it is printed with a wide margin, as the formatter would otherwise reject the
// nested boxes to the left and break the layout-sensitive Lean syntax.

pub fn parse(s: &str) -> Option<u32> {
    match s {
        "name0" => Some(0),
        "name1" => Some(1),
        "name2" => Some(2),
        "name3" => Some(3),
        "name4" => Some(4),
        "name5" => Some(5),
        "name6" => Some(6),
        "name7" => Some(7),
        "name8" => Some(8),
        "name9" => Some(9),
        "name10" => Some(10),
        "name11" => Some(11),
        "name12" => Some(12),
        "name13" => Some(13),
        "name14" => Some(14),
        "name15" => Some(15),
        _ => None,
    }
}

#[verify::test]
pub fn test_parse() {
    assert!(parse("name0") == Some(0));
    assert!(parse("name15") == Some(15));
    assert!(parse("other").is_none());
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_parse() {
        super::test_parse();
    }
}
