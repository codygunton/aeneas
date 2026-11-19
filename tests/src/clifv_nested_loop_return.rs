//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// `return` inside nested loops (lowered by the `lower_loop_exits` pre-pass).

/// The first pair `(i, j)`, `i < j < n`, with `i * j == target`, encoded as `i * 100 + j`;
/// `u32::MAX` if there is none.
pub fn find_pair(n: u32, target: u32) -> u32 {
    let mut i: u32 = 0;
    while i < n {
        let mut j: u32 = i + 1;
        while j < n {
            if i * j == target {
                return i * 100 + j;
            }
            j += 1;
        }
        i += 1;
    }
    u32::MAX
}

#[verify::test]
pub fn test_find_pair() {
    // Rust results: 12 = 2 * 6 (first with i < j: (2, 6)); 7 has no pair below 5.
    assert!(find_pair(10, 12) == 206);
    assert!(find_pair(5, 7) == u32::MAX);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_find_pair() {
        super::test_find_pair();
    }
}
