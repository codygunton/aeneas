/- `alloc::vec`: further `Vec` operations, `vec::Drain`, `vec::IntoIter` iterator methods.

Capacity is not tracked by the `Vec` model: `capacity` returns the length (Rust only guarantees
`capacity() >= len()`), `reserve`/`try_reserve` only check for capacity overflow. Allocation
failure (an abort in Rust) is not modelled. -/
module
public import Aeneas.Std.Alloc.Vec
public import Aeneas.Std.Alloc.Vec.IntoIter
public import Aeneas.Std.Alloc.Slice
public import Aeneas.Std.Alloc.Util
public import Aeneas.Std.Alloc.Collections.TryReserveError
public import Aeneas.Std.Core.Hash
public import Aeneas.Std.Core.RangeBounds
public import Aeneas.Std.SliceIter
public section

namespace Aeneas.Std

open Result AllocModel

/-! ## `Vec` methods -/

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::capacity"]
def alloc.vec.Vec.capacity {T : Type _} (A : Type _) (v : alloc.vec.Vec T) : Result Usize :=
  ok v.len

/-- Rust panics with "capacity overflow" when `len + additional` exceeds `isize::MAX` (the
    exact bound depends on `size_of::<T>()`, which is not modelled: this is the bound for
    one-byte elements). -/
@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::reserve"]
def alloc.vec.Vec.reserve {T : Type _} (A : Type _) (v : alloc.vec.Vec T) (additional : Usize) :
    Result (alloc.vec.Vec T) :=
  if v.length + additional.val ≤ Isize.max then ok v else fail .panic

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::try_reserve"]
def alloc.vec.Vec.try_reserve {T : Type _} (A : Type _) (v : alloc.vec.Vec T)
    (additional : Usize) :
    Result ((core.result.Result Unit alloc.collections.TryReserveError) × (alloc.vec.Vec T)) :=
  if v.length + additional.val ≤ Isize.max then ok (.Ok (), v)
  else ok (.Err .CapacityOverflow, v)

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::into_boxed_slice"]
def alloc.vec.Vec.into_boxed_slice {T : Type _} (A : Type _) (v : alloc.vec.Vec T) :
    Result (Slice T) :=
  ok v.slice

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::as_slice"]
def alloc.vec.Vec.as_slice {T : Type _} (A : Type _) (v : alloc.vec.Vec T) : Result (Slice T) :=
  ok (alloc.vec.Vec.deref v)

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::as_mut_slice"]
def alloc.vec.Vec.as_mut_slice {T : Type _} (A : Type _) (v : alloc.vec.Vec T) :
    Result ((Slice T) × (Slice T → alloc.vec.Vec T)) :=
  ok (alloc.vec.Vec.deref_mut v)

/-- Panics if `index >= len`. -/
@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove {T : Type _} (A : Type _) (v : alloc.vec.Vec T) (index : Usize) :
    Result (T × (alloc.vec.Vec T)) :=
  match v.val[index.val]? with
  | none => fail .panic
  | some x => do
    let v' ← vec (v.val.eraseIdx index.val)
    ok (x, v')

/-- Visits the elements in order, calling `f` exactly once on each; keeps those for which it
    returns `true`. -/
@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::retain"]
def alloc.vec.Vec.retain {T : Type _} (A : Type _) {F : Type _}
    (fnInst : core.ops.function.FnMut F T Bool) (v : alloc.vec.Vec T) (f : F) :
    Result (alloc.vec.Vec T) := do
  let l ← retainList fnInst.call_mut f [] v.val
  vec l

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::pop"]
def alloc.vec.Vec.pop {T : Type _} (A : Type _) (v : alloc.vec.Vec T) :
    Result ((Option T) × (alloc.vec.Vec T)) :=
  match v.val.getLast? with
  | none => ok (none, v)
  | some x => do
    let v' ← vec v.val.dropLast
    ok (some x, v')

/-- Moves all the elements of `other` to the end of `self`, leaving `other` empty.
    Output: (new `self`, new `other`). -/
@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::append"]
def alloc.vec.Vec.append {T : Type _} (A : Type _) (v other : alloc.vec.Vec T) :
    Result ((alloc.vec.Vec T) × (alloc.vec.Vec T)) :=
  if v.length + other.length ≤ Isize.max then do
    let v' ← vec (v.val ++ other.val)
    ok (v', alloc.vec.Vec.new T)
  else fail .panic

/-- `core::slice::range(range, ..len)`: panics when the bounds are out of order or exceed
    `len`. -/
@[expose] def AllocModel.sliceRange {R : Type _}
    (inst : core.ops.range.RangeBounds R Usize) (r : R) (len : Nat) : Result (Nat × Nat) := do
  let sb ← inst.start_bound r
  let eb ← inst.end_bound r
  let e ← match eb with
    | .Included e => if e.val ≥ len then fail .panic else ok (e.val + 1)
    | .Excluded e => if e.val > len then fail .panic else ok e.val
    | .Unbounded => ok len
  let s ← match sb with
    | .Excluded s => if s.val ≥ e then fail .panic else ok (s.val + 1)
    | .Included s => if s.val > e then fail .panic else ok s.val
    | .Unbounded => ok 0
  ok (s, e)

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"]
def alloc.vec.Vec.clear {T : Type _} (A : Type _) (_ : alloc.vec.Vec T) :
    Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

/-! ## `vec::Drain` -/

/-- The drained elements not yet yielded. The source `Vec` no longer contains them (the whole
    range is removed when the `Drain` is dropped, yielded or not). -/
@[rust_type "alloc::vec::drain::Drain" (body := .opaque)]
structure alloc.vec.drain.Drain (T : Type u) (A : Type v) where
  elems : List T

/-- Output: (drain iterator, the `Vec` with the range removed). -/
@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::drain"]
def alloc.vec.Vec.drain {T : Type _} (A : Type _) {R : Type _}
    (rangeBoundsInst : core.ops.range.RangeBounds R Usize) (v : alloc.vec.Vec T) (r : R) :
    Result ((alloc.vec.drain.Drain T A) × (alloc.vec.Vec T)) := do
  let (s, e) ← sliceRange rangeBoundsInst r v.length
  let v' ← vec (v.val.take s ++ v.val.drop e)
  ok ({ elems := (v.val.drop s).take (e - s) }, v')

@[expose, rust_fun
  "alloc::vec::drain::{core::iter::traits::iterator::Iterator<alloc::vec::drain::Drain<'0, @T, @A>, @T>}::size_hint"]
def alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.size_hint {T : Type _} {A : Type _}
    (d : alloc.vec.drain.Drain T A) : Result (Usize × (Option Usize)) :=
  exactSizeHint d.elems.length

@[expose, rust_fun
  "alloc::vec::drain::{core::iter::traits::iterator::Iterator<alloc::vec::drain::Drain<'0, @T, @A>, @T>}::next"]
def alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.next {T : Type _} {A : Type _}
    (d : alloc.vec.drain.Drain T A) : Result ((Option T) × (alloc.vec.drain.Drain T A)) :=
  match d.elems with
  | [] => ok (none, d)
  | x :: xs => ok (some x, { elems := xs })

@[expose, rust_fun
  "alloc::vec::drain::{core::iter::traits::double_ended::DoubleEndedIterator<alloc::vec::drain::Drain<'0, @T, @A>, @T>}::next_back"]
def alloc.vec.drain.Drain.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
    {T : Type _} {A : Type _} (d : alloc.vec.drain.Drain T A) :
    Result ((Option T) × (alloc.vec.drain.Drain T A)) :=
  match d.elems.getLast? with
  | none => ok (none, d)
  | some x => ok (some x, { elems := d.elems.dropLast })

/-! ## `vec::IntoIter` iterator methods (the allocator parameter is dropped, as for
`alloc.vec.into_iter.IntoIter`) -/

@[expose, rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::fold"
  (keepParams := [true, false, true, true])]
def alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
    {T : Type _} {B : Type _} {F : Type _}
    (fnInst : core.ops.function.FnMut F (B × T) B)
    (it : alloc.vec.into_iter.IntoIter T) (init : B) (f : F) : Result B :=
  foldList fnInst.call_mut f init (alloc.vec.Vec.val it)

@[expose, rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::last"
  (keepParams := [true, false])]
def alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.last {T : Type _}
    (it : alloc.vec.into_iter.IntoIter T) : Result (Option T) :=
  ok (alloc.vec.Vec.val it).getLast?

@[expose, rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::count"
  (keepParams := [true, false])]
def alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.count {T : Type _}
    (it : alloc.vec.into_iter.IntoIter T) : Result Usize :=
  ok (alloc.vec.Vec.len it)

/-! ## Trait implementations for `Vec` -/

/-- `impl Hash for [T]`: `state.write_length_prefix(len); T::hash_slice(self, state)`. -/
@[expose, rust_fun "alloc::vec::{core::hash::Hash<alloc::vec::Vec<@T>>}::hash"]
def alloc.vec.Vec.Insts.CoreHashHash.hash {T : Type _} (A : Type _) {H : Type _}
    (hashInst : core.hash.Hash T) (hasherInst : core.hash.Hasher H)
    (v : alloc.vec.Vec T) (state : H) : Result H := do
  let state ← hasherInst.write_length_prefix state v.len
  hashInst.hash_slice hasherInst v.slice state

@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter {T : Type _}
    (A : Type _) (v : alloc.vec.Vec T) : Result (core.slice.iter.Iter T) :=
  core.slice.Slice.iter v.slice

@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a mut alloc::vec::Vec<@T>, &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"]
def MutAVec.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter {T : Type _}
    (A : Type _) (v : alloc.vec.Vec T) :
    Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → alloc.vec.Vec T)) := do
  let (it, back) ← core.slice.Slice.iter_mut v.slice
  ok (it, fun it => { slice := back it })

/-- Appends every item of the iterator, in order. -/
@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::Extend<alloc::vec::Vec<@T>, @T>}::extend"]
def alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend {T : Type _} (A : Type _)
    {I : Type _} {Clause0_IntoIter : Type _}
    (intoIterInst : core.iter.traits.collect.IntoIterator I T Clause0_IntoIter)
    (v : alloc.vec.Vec T) (iter : I) : Result (alloc.vec.Vec T) := do
  let it ← intoIterInst.into_iter iter
  let l ← iterToList intoIterInst.iteratorInst it []
  vec (v.val ++ l)

/-- `Extend<&T>` for `T: Copy`: copies every item (no `clone` call), in order. -/
@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::Extend<alloc::vec::Vec<@T>, &'a @T>}::extend"]
def alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend {T : Type _} (A : Type _)
    {I : Type _} {Clause1_IntoIter : Type _} (_copyInst : core.marker.Copy T)
    (intoIterInst : core.iter.traits.collect.IntoIterator I T Clause1_IntoIter)
    (v : alloc.vec.Vec T) (iter : I) : Result (alloc.vec.Vec T) := do
  let it ← intoIterInst.into_iter iter
  let l ← iterToList intoIterInst.iteratorInst it []
  vec (v.val ++ l)

/-- Lexicographic order (`SliceOrd::compare`), then by length. -/
@[expose, rust_fun "alloc::vec::{core::cmp::Ord<alloc::vec::Vec<@T>>}::cmp"]
def alloc.vec.Vec.Insts.CoreCmpOrd.cmp {T : Type _} (A : Type _) (ordInst : core.cmp.Ord T)
    (v w : alloc.vec.Vec T) : Result Ordering :=
  lexCmp ordInst.cmp v.val w.val

@[expose, rust_fun "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.Insts.CoreDefaultDefault.default (T : Type _) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

/-- `Vec::from(&[T])`: clones the elements in order. -/
@[expose, rust_fun "alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, &'0 [@T]>}::from"]
def alloc.vec.Vec.Insts.CoreConvertFromShared0Slice.from {T : Type _}
    (cloneInst : core.clone.Clone T) (s : Slice T) : Result (alloc.vec.Vec T) :=
  alloc.slice.Slice.to_vec cloneInst s

end Aeneas.Std
