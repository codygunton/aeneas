//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// `continue` to an outer loop (lowered by the `lower_loop_exits` pre-pass).

/// The number of rows of a 4x4 grid (row-major) which contain no zero.
pub fn rows_without_zero(grid: [u32; 16]) -> u32 {
    let mut count: u32 = 0;
    let mut row: u32 = 0;
    'rows: while row < 4 {
        let r = row;
        row += 1;
        let mut col: u32 = 0;
        while col < 4 {
            if grid[(r * 4 + col) as usize] == 0 {
                continue 'rows;
            }
            col += 1;
        }
        count += 1;
    }
    count
}

#[verify::test]
pub fn test_rows_without_zero() {
    let mut grid = [1u32; 16];
    grid[1] = 0;
    grid[14] = 0;
    // Rust result: rows 0 and 3 contain a zero, so 2 rows have none.
    assert!(rows_without_zero(grid) == 2);
    assert!(rows_without_zero([1u32; 16]) == 4);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_rows_without_zero() {
        super::test_rows_without_zero();
    }
}
