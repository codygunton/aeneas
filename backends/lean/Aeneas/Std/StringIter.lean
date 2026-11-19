module
public import Aeneas.Std.String
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.SliceIter
public import Aeneas.Std.CoreStr
public section

namespace Aeneas.Std

@[rust_type "core::str::iter::Chars" (body := .opaque)]
structure core.str.iter.Chars where
  iter : core.slice.iter.Iter U8

/-- Decode the next character of the remaining (valid UTF-8) bytes. -/
@[expose, rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::next"]
def core.str.iter.IteratorChars.next (it : core.str.iter.Chars) :
    Result ((Option Char) × core.str.iter.Chars) :=
  match utf8First ((Str.bytes it.iter.slice).drop it.iter.i) with
  | none => .ok (none, it)
  | some (c, w) => .ok (some c, { iter := { it.iter with i := it.iter.i + w } })

@[expose, reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>"]
def core.iter.traits.iterator.IteratorChars :
  core.iter.traits.iterator.Iterator core.str.iter.Chars Char := {
  next := core.str.iter.IteratorChars.next
}

/-- `Chars` does not override `collect`: this is `Iterator::collect`. -/
@[expose, rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect"]
def core.str.iter.IteratorChars.collect
  {B : Type _} (itertraitscollectFromIteratorBCharInst :
  core.iter.traits.collect.FromIterator B Char) :
  core.str.iter.Chars → Result B :=
  core.iter.traits.iterator.Iterator.collect.default core.iter.traits.iterator.IteratorChars
    itertraitscollectFromIteratorBCharInst

@[expose, rust_fun "core::str::{str}::chars"]
def core.str.Str.chars (s : Str) : Result core.str.iter.Chars :=
  .ok { iter := { slice := s, i := 0 } }

end Aeneas.Std
