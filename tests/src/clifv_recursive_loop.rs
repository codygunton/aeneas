//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// A recursive function which calls itself from inside a loop (Cranelift's
// `bforest::NodePool::free_tree`): the `partial_fixpoint` definition needs `loop` to be
// monotone in its body (`Aeneas.Std.loop_mono`).

/// Number of nodes of the complete tree of the given depth and fan-out.
pub fn count_nodes(depth: u32, fanout: u32) -> u32 {
    let mut total = 1;
    if depth > 0 {
        for _ in 0..fanout {
            total += count_nodes(depth - 1, fanout);
        }
    }
    total
}

#[verify::test]
pub fn test_count_nodes() {
    assert!(count_nodes(0, 3) == 1);
    assert!(count_nodes(2, 3) == 13);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_count_nodes() {
        super::test_count_nodes();
    }
}
