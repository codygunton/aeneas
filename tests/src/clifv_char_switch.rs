//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Matches and comparisons on `char`s (the shapes of `cranelift_reader::lexer`):
// a switch over a char scrutinee, and char ranges (`'0'..='9'`).

pub fn classify(c: Option<char>) -> u32 {
    match c {
        None | Some('\n') => 0,
        Some(';') => 1,
        Some('0'..='9') => 2,
        Some('a'..='z') | Some('_') => 3,
        Some('é') => 4,
        _ => 5,
    }
}

pub fn looking_at_numeric(c: Option<char>) -> bool {
    if let Some(c) = c {
        match c {
            '0'..='9' => return true,
            '-' => return true,
            '+' => return true,
            '.' => return true,
            _ => {}
        }
    }
    false
}

pub fn count_digits(s: &[char]) -> u32 {
    let mut n = 0;
    let mut i = 0;
    while i < s.len() {
        if s[i] >= '0' && s[i] <= '9' {
            n += 1;
        }
        i += 1;
    }
    n
}

#[verify::test]
pub fn test_classify() {
    assert!(classify(None) == 0);
    assert!(classify(Some('\n')) == 0);
    assert!(classify(Some(';')) == 1);
    assert!(classify(Some('7')) == 2);
    assert!(classify(Some('q')) == 3);
    assert!(classify(Some('_')) == 3);
    assert!(classify(Some('é')) == 4);
    assert!(classify(Some('Z')) == 5);
}

#[verify::test]
pub fn test_looking_at_numeric() {
    assert!(looking_at_numeric(Some('5')));
    assert!(looking_at_numeric(Some('-')));
    assert!(looking_at_numeric(Some('.')));
    assert!(!looking_at_numeric(Some('x')));
    assert!(!looking_at_numeric(None));
}

#[verify::test]
pub fn test_count_digits() {
    assert!(count_digits(&['a', '1', '9', '/', ':', '0']) == 3);
}
