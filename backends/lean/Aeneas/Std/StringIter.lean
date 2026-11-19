module
public import Aeneas.Std.String
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.SliceIter
public section

namespace Aeneas.Std

@[rust_type "core::str::iter::Chars" (body := .opaque)]
structure core.str.iter.Chars where
  iter : core.slice.iter.Iter U8

-- TODO:
@[rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::next"]
opaque core.str.iter.IteratorChars.next (_iter : core.str.iter.Chars) : Result ((Option Char) × core.str.iter.Chars)

-- TODO:
@[rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect"]
opaque core.str.iter.IteratorChars.collect
  {B : Type _} (itertraitscollectFromIteratorBCharInst :
  core.iter.traits.collect.FromIterator B Char) :
  core.str.iter.Chars → Result B

/-- `Chars::size_hint` (`str/iter.rs`): `((len + 3) / 4, Some(len))` for `len` remaining bytes. -/
@[expose, rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::size_hint"]
def core.str.iter.IteratorChars.size_hint (it : core.str.iter.Chars) :
  Result (Usize × (Option Usize)) :=
  let len := it.iter.slice.val.length - it.iter.i
  .ok (Usize.satOfNat ((len + 3) / 4), some (Usize.satOfNat len))

@[expose, reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>"]
def core.iter.traits.iterator.IteratorChars :
  core.iter.traits.iterator.Iterator core.str.iter.Chars Char := {
  next := core.str.iter.IteratorChars.next
  size_hint := core.str.iter.IteratorChars.size_hint
}

@[expose, rust_fun "core::str::{str}::chars"]
def core.str.Str.chars (s : Str) : Result core.str.iter.Chars :=
  .ok { iter := { slice := s, i := 0 } }

end Aeneas.Std
