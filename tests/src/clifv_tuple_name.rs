//@ [!lean] skip
//@ [lean] aeneas-args=-print-unknown-externals
// `-print-unknown-externals` prints the name pattern of every external item
// without a model. Some names (here: an impl on a tuple type, reached through
// `PartialEq` on a pair) have no pattern syntax; the printer must print
// `<unprintable name>` instead of crashing.

pub fn eq_pairs(a: (u32, u32), b: (u32, u32)) -> bool {
    a == b
}
