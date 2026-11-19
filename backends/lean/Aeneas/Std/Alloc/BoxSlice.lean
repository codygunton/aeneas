/- `alloc::boxed`: `Box<[T]>` (a `Slice T`, boxes are erased) and `Box<MaybeUninit<T>>`. -/
module
public import Aeneas.Std.Alloc.Boxed
public import Aeneas.Std.Core.Mem
public import Aeneas.Std.SliceIter
public section

namespace Aeneas.Std

open Result

/-- `Box::<[T]>::from(&[T])`: clones the elements in order. -/
@[expose, rust_fun "alloc::boxed::convert::{core::convert::From<Box<[@T]>, &'0 [@T]>}::from"]
def BoxSlice.Insts.CoreConvertFromShared0Slice.from {T : Type _}
    (cloneInst : core.clone.Clone T) (s : Slice T) : Result (Slice T) :=
  Slice.clone cloneInst.clone s

@[expose, rust_fun
  "alloc::boxed::iter::{core::iter::traits::collect::IntoIterator<&'a mut Box<[@T]>, &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"]
def MutABoxSlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter {T : Type _}
    (A : Type _) (s : Slice T) :
    Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → Slice T)) :=
  core.slice.Slice.iter_mut s

/-- A fresh uninitialized box. -/
@[expose, rust_fun "alloc::boxed::{Box<@T>}::new_uninit"]
def alloc.boxed.Box.new_uninit (T : Type _) : Result (core.mem.maybe_uninit.MaybeUninit T) :=
  ok { value := none }

/-- Reading uninitialized memory is undefined behaviour in Rust: fails with `.panic`. -/
@[expose, rust_fun "alloc::boxed::{Box<core::mem::maybe_uninit::MaybeUninit<@T>>}::assume_init"]
def alloc.boxed.BoxMaybeUninit.assume_init {T : Type _} (A : Type _)
    (b : core.mem.maybe_uninit.MaybeUninit T) : Result T :=
  match b.value with
  | some x => ok x
  | none => fail .panic

@[expose, rust_fun "alloc::boxed::{core::default::Default<Box<[@T]>>}::default"]
def BoxSlice.Insts.CoreDefaultDefault.default (T : Type _) : Result (Slice T) :=
  ok (Slice.new T)

/-- Clones the elements in order (the allocator is `Global`, whose clone is trivial). -/
@[expose, rust_fun "alloc::boxed::{core::clone::Clone<Box<[@T]>>}::clone"]
def BoxSlice.Insts.CoreCloneClone.clone {T : Type _} {A : Type _}
    (cloneInst : core.clone.Clone T) (_cloneInst1 : core.clone.Clone A) (s : Slice T) :
    Result (Slice T) :=
  Slice.clone cloneInst.clone s

end Aeneas.Std
