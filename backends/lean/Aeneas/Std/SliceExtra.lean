/- `core::slice` functions and slice iterators (Rust 1.96). -/
module
public import Aeneas.Std.SliceIter
public import Aeneas.Std.Core.IterModel
public section

@[expose] section

namespace Aeneas.Std

open Result IterModel core.ops.range

/-- A slice from a list; the fallback is unreachable for sublists/rearrangements of a slice. -/
def Slice.ofListOr {α : Type u} (l : List α) (dflt : Slice α) : Slice α :=
  if h : l.length ≤ Usize.max then .from l h else dflt

/-- `s` with `s[start .. start + c.len]` replaced by `c` (back functions of `&mut [T]`). -/
def Slice.setRange {α : Type u} (s : Slice α) (start : Nat) (c : List α) : Slice α :=
  Slice.ofListOr (s.val.take start ++ c ++ s.val.drop (start + c.length)) s

/-! ## `slice::Iter` -/

/-- `Iter::position` (`iterator!` macro): counts from the current front. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::position"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.position
  {T : Type _} {P : Type _}
  (opsfunctionFnMutPTupleSharedATBoolInst : core.ops.function.FnMut P T Bool) :
  core.slice.iter.Iter T → P → Result ((Option Std.Usize) × (core.slice.iter.Iter T)) :=
  fun it p => do
    let (r, it) ← tryFoldNext core.slice.iter.IteratorSliceIter.next it (0, p) (fun (i, p) x => do
      let (b, p) ← opsfunctionFnMutPTupleSharedATBoolInst.call_mut p x
      if b then ok (.inr i) else ok (.inl (i + 1, p)))
    match r with
    | .inl _ => ok (none, it)
    | .inr i => ok (some (Usize.satOfNat i), it)

/-- `Iter::rposition`: `let mut i = len; while let Some(x) = self.next_back() { i -= 1;
    if predicate(x) { return Some(i) } }`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::rposition"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rposition
  {T : Type _} {P : Type _} {Clause1_Clause0_Item : Type _} {Clause2_Clause0_Item : Type _}
  (opsfunctionFnMutPTupleClause1_Clause0_ItemBoolInst : core.ops.function.FnMut P T Bool)
  (_itertraitsexact_sizeExactSizeIteratorIterClause1_Clause0_ItemInst :
    core.iter.traits.exact_size.ExactSizeIterator (core.slice.iter.Iter T) Clause1_Clause0_Item)
  (_itertraitsdouble_endedDoubleEndedIteratorIterClause2_Clause0_ItemInst :
    core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.Iter T)
      Clause2_Clause0_Item) :
  core.slice.iter.Iter T → P → Result ((Option Std.Usize) × (core.slice.iter.Iter T)) :=
  fun it p => do
    let n := it.slice.val.length - it.i
    let (r, it) ← tryFoldNext core.slice.iter.IteratorSliceIter.next_back it (n, p)
      (fun (i, p) x => do
        let i := i - 1
        let (b, p) ← opsfunctionFnMutPTupleClause1_Clause0_ItemBoolInst.call_mut p x
        if b then ok (.inr i) else ok (.inl (i, p)))
    match r with
    | .inl _ => ok (none, it)
    | .inr i => ok (some (Usize.satOfNat i), it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::find_map"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find_map
  {T : Type _} {B : Type _} {F : Type _}
  (opsfunctionFnMutFTupleSharedATOptionInst : core.ops.function.FnMut F T (Option B)) :
  core.slice.iter.Iter T → F → Result ((Option B) × (core.slice.iter.Iter T)) :=
  fun it f => do
    let (r, it, _) ← findMapNext core.slice.iter.IteratorSliceIter.next
      opsfunctionFnMutFTupleSharedATOptionInst.call_mut it f
    ok (r, it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
  {T : Type _} {F : Type _}
  (opsfunctionFnMutFTupleSharedATBoolInst : core.ops.function.FnMut F T Bool) :
  core.slice.iter.Iter T → F → Result (Bool × (core.slice.iter.Iter T)) :=
  fun it f => do
    let (r, it) ← tryFoldNext core.slice.iter.IteratorSliceIter.next it f (fun f x => do
      let (b, f) ← opsfunctionFnMutFTupleSharedATBoolInst.call_mut f x
      if b then ok (.inr ()) else ok (.inl f))
    match r with
    | .inl _ => ok (false, it)
    | .inr _ => ok (true, it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::all"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
  {T : Type _} {F : Type _}
  (opsfunctionFnMutFTupleSharedATBoolInst : core.ops.function.FnMut F T Bool) :
  core.slice.iter.Iter T → F → Result (Bool × (core.slice.iter.Iter T)) :=
  fun it f => do
    let (r, it) ← tryFoldNext core.slice.iter.IteratorSliceIter.next it f (fun f x => do
      let (b, f) ← opsfunctionFnMutFTupleSharedATBoolInst.call_mut f x
      if b then ok (.inl f) else ok (.inr ()))
    match r with
    | .inl _ => ok (true, it)
    | .inr _ => ok (false, it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::fold"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
  {T : Type _} {B : Type _} {F : Type _}
  (opsfunctionFnMutFPairBSharedATBInst : core.ops.function.FnMut F (B × T) B) :
  core.slice.iter.Iter T → B → F → Result B :=
  fun it acc f => do
    let (acc, _) ← foldNext core.slice.iter.IteratorSliceIter.next it (acc, f)
      (fun (acc, f) x => opsfunctionFnMutFPairBSharedATBInst.call_mut f (acc, x))
    ok acc

/-- `Iter::nth`: `if n < len { skip n, next } else { exhaust; None }`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::nth"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.nth
  {T : Type _} :
  core.slice.iter.Iter T → Std.Usize → Result ((Option T) × (core.slice.iter.Iter T)) :=
  fun it n =>
    if it.i + n.val < it.slice.val.length then
      core.slice.iter.IteratorSliceIter.next { it with i := it.i + n.val }
    else ok (none, { it with i := Nat.max it.i it.slice.val.length })

/-- `Iter::last`: `self.next_back()`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::last"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.last
  {T : Type _} : core.slice.iter.Iter T → Result (Option T) :=
  fun it => do
    let (o, _) ← core.slice.iter.IteratorSliceIter.next_back it
    ok o

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::count"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.count
  {T : Type _} : core.slice.iter.Iter T → Result Std.Usize :=
  fun it => ok (Usize.satOfNat (it.slice.val.length - it.i))

@[rust_fun
  "core::slice::iter::{core::iter::traits::exact_size::ExactSizeIterator<core::slice::iter::Iter<'0, @T>, &'_ @T>}::len"]
def core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT.len
  {T : Type _} : core.slice.iter.Iter T → Result Std.Usize :=
  fun it => ok (Usize.satOfNat (it.slice.val.length - it.i))

/-! ## `slice::IterMut`

The element closures (`FnMut(&mut T)`) cannot write the element back through the `FnMut`
model, so the backward functions for the `'a` loans are the identity. -/

@[rust_fun
  "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a mut [@T], &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"]
def MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
  {T : Type _} : Slice T → Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → Slice T)) :=
  fun s => ok ({ slice := s }, fun it => it.slice)

/-- Forward step of an `IterMut` without the backward function. -/
def core.slice.iter.IterMut.step {T : Type _} (it : core.slice.iter.IterMut T) :
    Result (Option T × core.slice.iter.IterMut T) := do
  let (o, it, _) ← core.slice.iter.IteratorIterMut.next it
  ok (o, it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::size_hint"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.size_hint
  {T : Type _} : core.slice.iter.IterMut T → Result (Std.Usize × (Option Std.Usize)) :=
  fun it =>
    let n := Usize.satOfNat (it.slice.val.length - it.i)
    ok (n, some n)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::position"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.position
  {T : Type _} {P : Type _}
  (opsfunctionFnMutPTupleMutATBoolInst : core.ops.function.FnMut P T Bool) :
  core.slice.iter.IterMut T → P →
    Result ((Option Std.Usize) × (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) :=
  fun it p => do
    let (r, it) ← tryFoldNext core.slice.iter.IterMut.step it (0, p) (fun (i, p) x => do
      let (b, p) ← opsfunctionFnMutPTupleMutATBoolInst.call_mut p x
      if b then ok (.inr i) else ok (.inl (i + 1, p)))
    match r with
    | .inl _ => ok (none, it, fun it => it)
    | .inr i => ok (some (Usize.satOfNat i), it, fun it => it)

/-- `IterMut::rposition`: the predicate is applied to the elements from the back as in Rust.
    The model's `IterMut` has no back cursor, so when an element is found the iterator state is
    left unchanged (Rust would also have consumed the elements from the found one to the end);
    when none is found the iterator is exhausted, as in Rust. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::rposition"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rposition
  {T : Type _} {P : Type _} {Clause1_Clause0_Item : Type _} {Clause2_Clause0_Item : Type _}
  (opsfunctionFnMutPTupleClause1_Clause0_ItemBoolInst : core.ops.function.FnMut P T Bool)
  (_itertraitsexact_sizeExactSizeIteratorIterMutClause1_Clause0_ItemInst :
    core.iter.traits.exact_size.ExactSizeIterator (core.slice.iter.IterMut T) Clause1_Clause0_Item)
  (_itertraitsdouble_endedDoubleEndedIteratorIterMutClause2_Clause0_ItemInst :
    core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T)
      Clause2_Clause0_Item) :
  core.slice.iter.IterMut T → P →
    Result ((Option Std.Usize) × (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) :=
  fun it p => do
    let rem := (it.slice.val.drop it.i).reverse
    let n := rem.length
    let (r, _) ← tryFoldNext (fun (l : List T) => ok (l.head?, l.tail)) rem (n, p)
      (fun (i, p) x => do
        let i := i - 1
        let (b, p) ← opsfunctionFnMutPTupleClause1_Clause0_ItemBoolInst.call_mut p x
        if b then ok (.inr i) else ok (.inl (i, p)))
    match r with
    | .inl _ => ok (none, { it with i := it.slice.val.length }, fun it => it)
    | .inr i => ok (some (Usize.satOfNat i), it, fun it => it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::find_map"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.find_map
  {T : Type _} {B : Type _} {F : Type _}
  (opsfunctionFnMutFTupleMutATOptionInst : core.ops.function.FnMut F T (Option B)) :
  core.slice.iter.IterMut T → F →
    Result ((Option B) × (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) :=
  fun it f => do
    let (r, it, _) ← findMapNext core.slice.iter.IterMut.step
      opsfunctionFnMutFTupleMutATOptionInst.call_mut it f
    ok (r, it, fun it => it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::any"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any
  {T : Type _} {F : Type _}
  (opsfunctionFnMutFTupleMutATBoolInst : core.ops.function.FnMut F T Bool) :
  core.slice.iter.IterMut T → F →
    Result (Bool × (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) :=
  fun it f => do
    let (r, it) ← tryFoldNext core.slice.iter.IterMut.step it f (fun f x => do
      let (b, f) ← opsfunctionFnMutFTupleMutATBoolInst.call_mut f x
      if b then ok (.inr ()) else ok (.inl f))
    match r with
    | .inl _ => ok (false, it, fun it => it)
    | .inr _ => ok (true, it, fun it => it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::all"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.all
  {T : Type _} {F : Type _}
  (opsfunctionFnMutFTupleMutATBoolInst : core.ops.function.FnMut F T Bool) :
  core.slice.iter.IterMut T → F →
    Result (Bool × (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) :=
  fun it f => do
    let (r, it) ← tryFoldNext core.slice.iter.IterMut.step it f (fun f x => do
      let (b, f) ← opsfunctionFnMutFTupleMutATBoolInst.call_mut f x
      if b then ok (.inl f) else ok (.inr ()))
    match r with
    | .inl _ => ok (true, it, fun it => it)
    | .inr _ => ok (false, it, fun it => it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::fold"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold
  {T : Type _} {B : Type _} {F : Type _}
  (opsfunctionFnMutFPairBMutATBInst : core.ops.function.FnMut F (B × T) B) :
  core.slice.iter.IterMut T → B → F → Result (B × (core.slice.iter.IterMut T)) :=
  fun it acc f => do
    let (acc, _) ← foldNext core.slice.iter.IterMut.step it (acc, f)
      (fun (acc, f) x => opsfunctionFnMutFPairBMutATBInst.call_mut f (acc, x))
    ok (acc, it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::nth"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.nth
  {T : Type _} :
  core.slice.iter.IterMut T → Std.Usize →
    Result ((Option T) × (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)) :=
  fun it n =>
    if it.i + n.val < it.slice.val.length then
      core.slice.iter.IteratorIterMut.next { it with i := it.i + n.val }
    else ok (none, { it with i := Nat.max it.i it.slice.val.length }, fun it _ => it)

/-- `IterMut::last` (consumes the iterator): the last remaining element, the backward function
    writes it back into the iterator's slice. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::last"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.last
  {T : Type _} :
  core.slice.iter.IterMut T → Result ((Option T) × (Option T → core.slice.iter.IterMut T)) :=
  fun it =>
    let n := it.slice.val.length
    if it.i < n then
      ok ((it.slice.val.drop it.i).getLast?, fun o =>
        match o with
        | none => it
        | some x => { it with slice := it.slice.setAtNat (n - 1) x })
    else ok (none, fun _ => it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::count"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.count
  {T : Type _} : core.slice.iter.IterMut T → Result (Std.Usize × (core.slice.iter.IterMut T)) :=
  fun it => ok (Usize.satOfNat (it.slice.val.length - it.i), it)

/-! ## `Windows` -/

/-- `Windows { v, size }`. -/
@[rust_type "core::slice::iter::Windows" (body := .opaque)]
structure core.slice.iter.Windows (T : Type u) where
  v : Slice T
  size : Usize

/-- `[T]::windows`: panics on a zero size. -/
@[rust_fun "core::slice::{[@T]}::windows"]
def core.slice.Slice.windows {T : Type _} : Slice T → Std.Usize → Result (core.slice.iter.Windows T) :=
  fun s size => if size.val = 0 then fail .panic else ok ⟨s, size⟩

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
  {T : Type _} : core.slice.iter.Windows T → Result ((Option (Slice T)) × (core.slice.iter.Windows T)) :=
  fun self =>
    if self.size.val > self.v.val.length then ok (none, self)
    else ok (some (Slice.ofListOr (self.v.val.take self.size.val) self.v),
      { self with v := Slice.ofListOr (self.v.val.drop 1) self.v })

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>}::size_hint"]
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.size_hint
  {T : Type _} : core.slice.iter.Windows T → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    if self.size.val > self.v.val.length then ok (0#usize, some 0#usize)
    else
      let n := Usize.satOfNat (self.v.val.length - self.size.val + 1)
      ok (n, some n)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>}::count"]
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.count
  {T : Type _} : core.slice.iter.Windows T → Result Std.Usize :=
  fun self => do
    let (n, _) ← core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.size_hint self
    ok n

/-- `Windows::nth`: `if let Some(rest) = v.get(n..) && let Some(nth) = rest.get(..size)
    { v = &rest[1..]; Some(nth) } else { v = &v[..0]; None }`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>}::nth"]
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.nth
  {T : Type _} :
  core.slice.iter.Windows T → Std.Usize → Result ((Option (Slice T)) × (core.slice.iter.Windows T)) :=
  fun self n =>
    let l := self.v.val
    if n.val ≤ l.length ∧ self.size.val ≤ l.length - n.val then
      let rest := l.drop n.val
      ok (some (Slice.ofListOr (rest.take self.size.val) self.v),
        { self with v := Slice.ofListOr (rest.drop 1) self.v })
    else ok (none, { self with v := Slice.ofListOr [] self.v })

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>}::last"]
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.last
  {T : Type _} : core.slice.iter.Windows T → Result (Option (Slice T)) :=
  fun self =>
    let l := self.v.val
    if self.size.val > l.length then ok none
    else ok (some (Slice.ofListOr (l.drop (l.length - self.size.val)) self.v))

/-! ## `ArrayWindows` -/

/-- `ArrayWindows { v }`. -/
@[rust_type "core::slice::iter::ArrayWindows" (body := .opaque)]
structure core.slice.iter.ArrayWindows (T : Type u) (N : Usize) where
  v : Slice T

/-- `[T]::array_windows::<N>`: `assert!(N != 0, "window size must be non-zero")`. -/
@[rust_fun "core::slice::{[@T]}::array_windows"]
def core.slice.Slice.array_windows {T : Type _} (N : Std.Usize) :
  Slice T → Result (core.slice.iter.ArrayWindows T N) :=
  fun s => if N.val = 0 then fail .panic else ok ⟨s⟩

/-- `first_chunk::<N>()`. -/
def core.slice.iter.ArrayWindows.firstChunk {T : Type u} {N : Usize} (l : List T) :
    Option (Array T N) :=
  if h : N.val ≤ l.length then some (Array.make N (l.take N.val) (by simp [h])) else none

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ArrayWindows<'a, @T, @N>, &'a [@T; @N]>}::next"]
def core.slice.iter.ArrayWindows.Insts.CoreIterTraitsIteratorIteratorSharedAArray.next
  {T : Type _} {N : Std.Usize} :
  core.slice.iter.ArrayWindows T N →
    Result ((Option (Array T N)) × (core.slice.iter.ArrayWindows T N)) :=
  fun self =>
    match core.slice.iter.ArrayWindows.firstChunk (N := N) self.v.val with
    | none => ok (none, self)
    | some a => ok (some a, ⟨Slice.ofListOr (self.v.val.drop 1) self.v⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ArrayWindows<'a, @T, @N>, &'a [@T; @N]>}::size_hint"]
def core.slice.iter.ArrayWindows.Insts.CoreIterTraitsIteratorIteratorSharedAArray.size_hint
  {T : Type _} {N : Std.Usize} :
  core.slice.iter.ArrayWindows T N → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    let n := Usize.satOfNat (self.v.val.length - (N.val - 1))
    ok (n, some n)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ArrayWindows<'a, @T, @N>, &'a [@T; @N]>}::count"]
def core.slice.iter.ArrayWindows.Insts.CoreIterTraitsIteratorIteratorSharedAArray.count
  {T : Type _} {N : Std.Usize} : core.slice.iter.ArrayWindows T N → Result Std.Usize :=
  fun self => ok (Usize.satOfNat (self.v.val.length - (N.val - 1)))

/-- `ArrayWindows::nth`: `let idx = n.min(v.len()); v = &v[idx..]; self.next()`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ArrayWindows<'a, @T, @N>, &'a [@T; @N]>}::nth"]
def core.slice.iter.ArrayWindows.Insts.CoreIterTraitsIteratorIteratorSharedAArray.nth
  {T : Type _} {N : Std.Usize} :
  core.slice.iter.ArrayWindows T N → Std.Usize →
    Result ((Option (Array T N)) × (core.slice.iter.ArrayWindows T N)) :=
  fun self n =>
    core.slice.iter.ArrayWindows.Insts.CoreIterTraitsIteratorIteratorSharedAArray.next
      ⟨Slice.ofListOr (self.v.val.drop n.val) self.v⟩

/-- `ArrayWindows::last`: `self.v.last_chunk()`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ArrayWindows<'a, @T, @N>, &'a [@T; @N]>}::last"]
def core.slice.iter.ArrayWindows.Insts.CoreIterTraitsIteratorIteratorSharedAArray.last
  {T : Type _} {N : Std.Usize} : core.slice.iter.ArrayWindows T N → Result (Option (Array T N)) :=
  fun self =>
    let l := self.v.val
    ok (core.slice.iter.ArrayWindows.firstChunk (N := N) (l.drop (l.length - N.val)))

/-! ## `ChunksExact` -/

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::count"]
def core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.count
  {T : Type _} : core.slice.iter.ChunksExact T → Result Std.Usize :=
  fun self => ok (Usize.satOfNat self.chunks.length)

/-- `ChunksExact::nth`: skip `n` chunks (exhausting the iterator if there are not enough),
    then `next`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::nth"]
def core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.nth
  {T : Type _} :
  core.slice.iter.ChunksExact T → Std.Usize →
    Result ((Option (Slice T)) × (core.slice.iter.ChunksExact T)) :=
  fun self n =>
    if n.val < self.chunks.length then
      core.slice.iter.IteratorChunksExact.next { self with chunks := self.chunks.drop n.val }
    else ok (none, { self with chunks := [] })

@[rust_fun
  "core::slice::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::ChunksExact<'a, @T>, &'_ [@T]>}::next_back"]
def core.slice.iter.ChunksExact.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedSlice.next_back
  {T : Type _} :
  core.slice.iter.ChunksExact T → Result ((Option (Slice T)) × (core.slice.iter.ChunksExact T)) :=
  fun self =>
    match self.chunks.getLast? with
    | none => ok (none, self)
    | some c => ok (some c, { self with chunks := self.chunks.dropLast })

/-- `ChunksExact::last`: `self.next_back()`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::last"]
def core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.last
  {T : Type _} : core.slice.iter.ChunksExact T → Result (Option (Slice T)) :=
  fun self => ok self.chunks.getLast?

/-! ## `ChunkByMut` -/

/-- `ChunkByMut { slice, predicate }`; the model keeps the whole slice and the start of the
    remaining part so that the backward functions can write chunks back. -/
@[rust_type "core::slice::iter::ChunkByMut" (mutRegions := #[0]) (body := .opaque)]
structure core.slice.iter.ChunkByMut (T : Type u) (P : Type v) where
  slice : Slice T
  start : Nat
  predicate : P

@[rust_fun "core::slice::{[@T]}::chunk_by_mut"]
def core.slice.Slice.chunk_by_mut {T : Type _} {F : Type _}
  (_opsfunctionFnMutFPairShared0TSharedTBoolInst : core.ops.function.FnMut F (T × T) Bool) :
  Slice T → F → Result ((core.slice.iter.ChunkByMut T F) × (core.slice.iter.ChunkByMut T F → Slice T)) :=
  fun s f => ok (⟨s, 0, f⟩, fun it => it.slice)

/-- Length of the next chunk: `len = 1; for [l, r] in windows(2) { if pred(l, r) { len += 1 }
    else { break } }`. -/
def core.slice.iter.ChunkByMut.chunkLen {T : Type u} {P : Type v}
    (call : P → T × T → Result (Bool × P)) : List T → Nat → P → Result (Nat × P)
  | l :: r :: rest, len, p => do
    let (b, p) ← call p (l, r)
    if b then core.slice.iter.ChunkByMut.chunkLen call (r :: rest) (len + 1) p else ok (len, p)
  | _, len, p => ok (len, p)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunkByMut<'a, @T, @P>, &'a mut [@T]>}::next"]
def core.slice.iter.ChunkByMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next
  {T : Type _} {P : Type _}
  (opsfunctionFnMutPPairSharedATShared0TBoolInst : core.ops.function.FnMut P (T × T) Bool) :
  core.slice.iter.ChunkByMut T P →
    Result ((Option (Slice T)) × (core.slice.iter.ChunkByMut T P) ×
      (core.slice.iter.ChunkByMut T P → Option (Slice T) → core.slice.iter.ChunkByMut T P)) :=
  fun self => do
    let rem := self.slice.val.drop self.start
    if rem.isEmpty then ok (none, self, fun it _ => it)
    else do
      let (len, p) ← core.slice.iter.ChunkByMut.chunkLen
        opsfunctionFnMutPPairSharedATShared0TBoolInst.call_mut rem 1 self.predicate
      let st := self.start
      ok (some (Slice.ofListOr (rem.take len) self.slice),
        { slice := self.slice, start := st + len, predicate := p },
        fun it o => match o with
          | none => it
          | some c => { it with slice := Slice.setRange it.slice st c.val })

/-! ## Slice methods -/

@[rust_fun "core::slice::{[@T]}::first"]
def core.slice.Slice.first {T : Type _} : Slice T → Result (Option T) :=
  fun s => ok s.val.head?

@[rust_fun "core::slice::{[@T]}::first_mut"]
def core.slice.Slice.first_mut {T : Type _} : Slice T → Result ((Option T) × (Option T → Slice T)) :=
  fun s => ok (s.val.head?, fun o => match o with
    | none => s
    | some x => s.setAtNat 0 x)

@[rust_fun "core::slice::{[@T]}::split_first"]
def core.slice.Slice.split_first {T : Type _} : Slice T → Result (Option (T × (Slice T))) :=
  fun s => match s.val with
    | [] => ok none
    | x :: xs => ok (some (x, Slice.ofListOr xs s))

@[rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type _} : Slice T → Result (Option T) :=
  fun s => ok s.val.getLast?

@[rust_fun "core::slice::{[@T]}::last_mut"]
def core.slice.Slice.last_mut {T : Type _} : Slice T → Result ((Option T) × (Option T → Slice T)) :=
  fun s => ok (s.val.getLast?, fun o => match o with
    | none => s
    | some x => s.setAtNat (s.val.length - 1) x)

/-- The loop of `binary_search_by`: `while size > 1 { half = size / 2; mid = base + half;
    base = if f(v[mid]) == Greater { base } else { mid }; size -= half }` (`fuel` bounds the
    number of iterations, which is at most `log2 len`). -/
def core.slice.binarySearchLoop {T : Type u} {F : Type v}
    (call : F → T → Result (Ordering × F)) (l : List T) :
    (size base : Nat) → F → (fuel : Nat) → Result (Nat × F)
  | _, base, f, 0 => ok (base, f)
  | size, base, f, fuel + 1 =>
    if size > 1 then do
      let half := size / 2
      let mid := base + half
      match l[mid]? with
      | none => fail .panic
      | some x => do
        let (c, f) ← call f x
        let base := if c = .gt then base else mid
        core.slice.binarySearchLoop call l (size - half) base f fuel
    else ok (base, f)

/-- `binary_search_by` (Rust 1.96 `core::slice`): the branch-free loop with a fixed number of
    iterations, then a final comparison at `base`. -/
@[rust_fun "core::slice::{[@T]}::binary_search_by"]
def core.slice.Slice.binary_search_by {T : Type _} {F : Type _}
  (opsfunctionFnMutFTupleSharedATOrderingInst : core.ops.function.FnMut F T Ordering) :
  Slice T → F → Result (core.result.Result Std.Usize Std.Usize) :=
  fun s f => do
    let l := s.val
    let call := opsfunctionFnMutFTupleSharedATOrderingInst.call_mut
    if l.length = 0 then ok (.Err 0#usize)
    else do
      let (base, f) ← core.slice.binarySearchLoop call l l.length 0 f l.length
      match l[base]? with
      | none => fail .panic
      | some x => do
        let (c, _) ← call f x
        if c = .eq then ok (.Ok (Usize.satOfNat base))
        else ok (.Err (Usize.satOfNat (base + (if c = .lt then 1 else 0))))

/-- `binary_search_by_key(b, f)`: `binary_search_by(|k| f(k).cmp(b))`. -/
@[rust_fun "core::slice::{[@T]}::binary_search_by_key"]
def core.slice.Slice.binary_search_by_key {T : Type _} {B : Type _} {F : Type _}
  (opsfunctionFnMutFTupleSharedATBInst : core.ops.function.FnMut F T B)
  (cmpOrdInst : core.cmp.Ord B) :
  Slice T → B → F → Result (core.result.Result Std.Usize Std.Usize) :=
  fun s b f =>
    core.slice.Slice.binary_search_by
      { FnOnceInst := { call_once := fun f x => do
          let (k, _) ← opsfunctionFnMutFTupleSharedATBInst.call_mut f x
          cmpOrdInst.cmp k b }
        call_mut := fun f x => do
          let (k, f) ← opsfunctionFnMutFTupleSharedATBInst.call_mut f x
          let c ← cmpOrdInst.cmp k b
          ok (c, f) } s f

/-- `partition_point(pred)`: `binary_search_by(|x| if pred(x) { Less } else { Greater })
    .unwrap_or_else(|i| i)`. -/
@[rust_fun "core::slice::{[@T]}::partition_point"]
def core.slice.Slice.partition_point {T : Type _} {P : Type _}
  (opsfunctionFnMutPTupleShared0TBoolInst : core.ops.function.FnMut P T Bool) :
  Slice T → P → Result Std.Usize :=
  fun s p => do
    let r ← core.slice.Slice.binary_search_by
      { FnOnceInst := { call_once := fun p x => do
          let (b, _) ← opsfunctionFnMutPTupleShared0TBoolInst.call_mut p x
          ok (if b then Ordering.lt else Ordering.gt) }
        call_mut := fun p x => do
          let (b, p) ← opsfunctionFnMutPTupleShared0TBoolInst.call_mut p x
          ok (if b then Ordering.lt else Ordering.gt, p) } s p
    match r with
    | .Ok i => ok i
    | .Err i => ok i

/-- Merge of two sorted lists: take from the right only when it is strictly smaller. -/
def core.slice.mergeBy {T : Type u} {σ : Type v} (lt : σ → T → T → Result (Bool × σ))
    (a b : List T) (s : σ) : Result (List T × σ) :=
  match a, b with
  | [], b => ok (b, s)
  | a, [] => ok (a, s)
  | x :: a', y :: b' => do
    let (c, s1) ← lt s y x
    if c then do
      let (r, s2) ← core.slice.mergeBy lt (x :: a') b' s1
      ok (y :: r, s2)
    else do
      let (r, s2) ← core.slice.mergeBy lt a' (y :: b') s1
      ok (x :: r, s2)
partial_fixpoint

/-- Stable merge sort under a strict "less than" with a threaded state; equal elements keep
    their order (a valid `sort_unstable` output). -/
def core.slice.mergeSortBy {T : Type u} {σ : Type v} (lt : σ → T → T → Result (Bool × σ))
    (l : List T) (s : σ) : Result (List T × σ) :=
  match l with
  | [] => ok ([], s)
  | [x] => ok ([x], s)
  | l => do
    let k := l.length / 2
    let (a, s1) ← core.slice.mergeSortBy lt (l.take k) s
    let (b, s2) ← core.slice.mergeSortBy lt (l.drop k) s1
    core.slice.mergeBy lt a b s2
partial_fixpoint

/-- `sort_unstable`: sorts with `T::lt`.

    Not the ipnsort algorithm of Rust 1.96: the output is a stable sort, which differs from
    Rust's only in the relative order of elements comparing `Equal`. At the Cranelift call
    sites (`regs.sort_unstable()` on `Writable<RealReg>` with derived `Ord`), `Equal` elements
    are identical, so the results coincide. -/
@[rust_fun "core::slice::{[@T]}::sort_unstable"]
def core.slice.Slice.sort_unstable {T : Type _} (cmpOrdInst : core.cmp.Ord T) :
  Slice T → Result (Slice T) :=
  fun s => do
    let (l, _) ← core.slice.mergeSortBy (fun (_ : Unit) a b => do
      let c ← cmpOrdInst.partialOrdInst.lt a b
      ok (c, ())) s.val ()
    ok (Slice.ofListOr l s)

/-- `sort_unstable_by_key(f)`: sorts with `|a, b| f(a).lt(&f(b))` (the key closure is called
    for both elements of every comparison, `a` first).

    Stable output (see `sort_unstable`): at the Cranelift call site the key
    `(class, Reverse(hw_enc))` determines the register, so equal keys are identical elements. -/
@[rust_fun "core::slice::{[@T]}::sort_unstable_by_key"]
def core.slice.Slice.sort_unstable_by_key {T : Type _} {K : Type _} {F : Type _}
  (opsfunctionFnMutFTupleShared0TKInst : core.ops.function.FnMut F T K)
  (cmpOrdInst : core.cmp.Ord K) :
  Slice T → F → Result (Slice T) :=
  fun s f => do
    let (l, _) ← core.slice.mergeSortBy (fun f a b => do
      let (ka, f) ← opsfunctionFnMutFTupleShared0TKInst.call_mut f a
      let (kb, f) ← opsfunctionFnMutFTupleShared0TKInst.call_mut f b
      let c ← cmpOrdInst.partialOrdInst.lt ka kb
      ok (c, f)) s.val f
    ok (Slice.ofListOr l s)

/-- `clone_from_slice(src)`: panics on a length mismatch, then clones `src` element by
    element. -/
@[rust_fun "core::slice::{[@T]}::clone_from_slice"]
def core.slice.Slice.clone_from_slice {T : Type _} (cloneCloneInst : core.clone.Clone T) :
  Slice T → Slice T → Result (Slice T) :=
  fun dst src =>
    if dst.val.length ≠ src.val.length then fail .panic
    else do
      let l ← List.mapM cloneCloneInst.clone src.val
      ok (Slice.ofListOr l dst)

/-- `<&[T] as Default>::default`: the empty slice. -/
@[rust_fun "core::slice::{core::default::Default<&'0 [@T]>}::default"]
def Shared0Slice.Insts.CoreDefaultDefault.default (T : Type _) : Result (Slice T) :=
  ok (.from [] (by scalar_tac))

@[rust_fun "core::slice::raw::from_ref"]
def core.slice.raw.from_ref {T : Type _} : T → Result (Slice T) :=
  fun x => ok (.from [x] (by scalar_tac))

@[rust_fun "core::slice::raw::from_mut"]
def core.slice.raw.from_mut {T : Type _} : T → Result ((Slice T) × (Slice T → T)) :=
  fun x => ok (.from [x] (by scalar_tac), fun s => match s.val with
    | y :: _ => y
    | [] => x)

/-! ## `SliceIndex<[T]> for RangeInclusive<usize>` -/

/-- `RangeInclusive::into_slice_range`: `start..end + 1` (start := end + 1 once exhausted);
    `none` when `end == usize::MAX` (the `get` path returns `None`, `index` panics). -/
def core.ops.range.RangeInclusiveUsize.toRange (r : core.ops.range.RangeInclusive Std.Usize) :
    Option (Nat × Nat) :=
  if r.«end».val = Usize.max then none
  else
    let e := r.«end».val + 1
    some (if r.exhausted then e else r.start.val, e)

@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get"]
def core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
  {T : Type _} : core.ops.range.RangeInclusive Std.Usize → Slice T → Result (Option (Slice T)) :=
  fun r s =>
    match core.ops.range.RangeInclusiveUsize.toRange r with
    | none => ok none
    | some (a, b) =>
      if a ≤ b ∧ b ≤ s.val.length then
        ok (some (Slice.ofListOr ((s.val.drop a).take (b - a)) s))
      else ok none

@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get_mut"]
def core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut
  {T : Type _} :
  core.ops.range.RangeInclusive Std.Usize → Slice T →
    Result ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  fun r s =>
    match core.ops.range.RangeInclusiveUsize.toRange r with
    | none => ok (none, fun _ => s)
    | some (a, b) =>
      if a ≤ b ∧ b ≤ s.val.length then
        ok (some (Slice.ofListOr ((s.val.drop a).take (b - a)) s), fun o => match o with
          | none => s
          | some c => Slice.setRange s a c.val)
      else ok (none, fun _ => s)

/-- `index`: panics (`slice_end_index_overflow_fail` / out of range). -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::index"]
def core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  {T : Type _} : core.ops.range.RangeInclusive Std.Usize → Slice T → Result (Slice T) :=
  fun r s => do
    let o ← core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get r s
    match o with
    | none => fail .panic
    | some x => ok x

@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::index_mut"]
def core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut
  {T : Type _} :
  core.ops.range.RangeInclusive Std.Usize → Slice T → Result ((Slice T) × (Slice T → Slice T)) :=
  fun r s =>
    match core.ops.range.RangeInclusiveUsize.toRange r with
    | none => fail .panic
    | some (a, b) =>
      if a ≤ b ∧ b ≤ s.val.length then
        ok (Slice.ofListOr ((s.val.drop a).take (b - a)) s, fun c => Slice.setRange s a c.val)
      else fail .panic

/-- `get_unchecked`: out-of-range is undefined behaviour. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get_unchecked"]
def core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked
  {T : Type _} :
  core.ops.range.RangeInclusive Std.Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  fun r p => do
    let o ← core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get r p.v
    match o with
    | none => fail .undef
    | some x => ok ⟨x⟩

@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  {T : Type _} :
  core.ops.range.RangeInclusive Std.Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  fun r p => do
    let o ← core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get r p.v
    match o with
    | none => fail .undef
    | some x => ok ⟨x⟩

end Aeneas.Std
