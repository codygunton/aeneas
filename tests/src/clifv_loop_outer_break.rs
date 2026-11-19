//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// `break` to an outer loop (lowered by the `lower_loop_exits` pre-pass).

/// The index of the first row containing `x` in a 4x4 grid stored row-major, or 4.
pub fn find_row(grid: [u32; 16], x: u32) -> u32 {
    let mut row: u32 = 0;
    'rows: while row < 4 {
        let mut col: u32 = 0;
        while col < 4 {
            if grid[(row * 4 + col) as usize] == x {
                break 'rows;
            }
            col += 1;
        }
        row += 1;
    }
    row
}

#[verify::test]
pub fn test_find_row() {
    let mut grid = [0u32; 16];
    let mut i = 0;
    while i < 16 {
        grid[i] = i as u32;
        i += 1;
    }
    // Rust results: 9 is in row 2; 100 is absent (4).
    assert!(find_row(grid, 9) == 2);
    assert!(find_row(grid, 100) == 4);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_find_row() {
        super::test_find_row();
    }
}
