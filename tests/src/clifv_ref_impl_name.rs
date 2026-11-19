//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// An impl for a reference to a crate's ADT named like a standard-library ADT
// (`allocator_api2`'s `impl IntoIterator for &Vec<T, A>`) must not get the name of the library's
// impl for the standard ADT (`SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter`):
// it is prefixed with the ADT's module path.

pub mod stable {
    pub struct Vec {
        pub items: [u32; 2],
    }

    impl<'a> IntoIterator for &'a Vec {
        type Item = &'a u32;
        type IntoIter = core::slice::Iter<'a, u32>;
        fn into_iter(self) -> Self::IntoIter {
            self.items.iter()
        }
    }
}

pub fn first_local(v: &stable::Vec) -> u32 {
    match v.into_iter().next() {
        Some(x) => *x,
        None => 0,
    }
}

pub fn first_std(v: &std::vec::Vec<u32>) -> u32 {
    match v.into_iter().next() {
        Some(x) => *x,
        None => 0,
    }
}

#[verify::test]
pub fn test_first() {
    let v = stable::Vec { items: [3, 4] };
    assert!(first_local(&v) == 3);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_first() {
        super::test_first();
        assert_eq!(super::first_std(&vec![5, 6]), 5);
    }
}
