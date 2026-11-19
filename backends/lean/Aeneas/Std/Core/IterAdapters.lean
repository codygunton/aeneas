module
public import Aeneas.Std.Core.IterModel
public import Aeneas.Std.Core.Default
public section

@[expose] section

/-! Models of the `core::iter` adapters and provided `Iterator` methods (Rust 1.96).

Every model calls the underlying iterators' `next`/`next_back` and the closures in exactly
the order of the standard library implementation, so stateful closures observe the same
sequence of calls; short-circuiting methods stop at the same element. -/

namespace Aeneas.Std

open Result IterModel

/-! ## Adapter types -/

@[rust_type "core::iter::adapters::filter::Filter" (body := .opaque)]
structure core.iter.adapters.filter.Filter (I : Type u) (P : Type v) where
  iter : I
  predicate : P

@[rust_type "core::iter::adapters::filter_map::FilterMap" (body := .opaque)]
structure core.iter.adapters.filter_map.FilterMap (I : Type u) (F : Type v) where
  iter : I
  f : F

@[rust_type "core::iter::adapters::skip::Skip" (body := .opaque)]
structure core.iter.adapters.skip.Skip (I : Type u) where
  iter : I
  n : Usize

@[rust_type "core::iter::adapters::skip_while::SkipWhile" (body := .opaque)]
structure core.iter.adapters.skip_while.SkipWhile (I : Type u) (P : Type v) where
  iter : I
  flag : Bool
  predicate : P

@[rust_type "core::iter::adapters::scan::Scan" (body := .opaque)]
structure core.iter.adapters.scan.Scan (I : Type u) (St : Type v) (F : Type w) where
  iter : I
  f : F
  state : St

/-- `Peekable { iter, peeked: Option<Option<I::Item>> }`. -/
@[rust_type "core::iter::adapters::peekable::Peekable" (body := .opaque)]
structure core.iter.adapters.peekable.Peekable (I : Type u) (Clause0_Item : Type v) where
  iter : I
  peeked : Option (Option Clause0_Item)

/-- `Fuse { iter: Option<I> }`: `None` once the inner iterator returned `None`. -/
@[rust_type "core::iter::adapters::fuse::Fuse" (body := .opaque)]
structure core.iter.adapters.fuse.Fuse (I : Type u) where
  iter : Option I

/-- `Flatten { inner: FlattenCompat { iter: Fuse<I>, frontiter, backiter } }`; the last
    parameter is the inner `IntoIter` type. -/
@[rust_type "core::iter::adapters::flatten::Flatten" (body := .opaque)]
structure core.iter.adapters.flatten.Flatten (I : Type u) (Clause0_Item : Type v)
    (Clause1_Item : Type w) (Clause1_IntoIter : Type x) where
  iter : Option I
  frontiter : Option Clause1_IntoIter
  backiter : Option Clause1_IntoIter

/-- `FlatMap { inner: FlattenCompat { iter: Fuse<Map<I, F>>, frontiter, backiter } }`. -/
@[rust_type "core::iter::adapters::flatten::FlatMap" (body := .opaque)]
structure core.iter.adapters.flatten.FlatMap (I : Type u) (U : Type v) (F : Type w)
    (Clause0_Item : Type x) (Clause0_IntoIter : Type y) where
  iter : Option (I × F)
  frontiter : Option Clause0_IntoIter
  backiter : Option Clause0_IntoIter

/-- `Chain { a: Option<A>, b: Option<B> }`. -/
@[rust_type "core::iter::adapters::chain::Chain" (body := .opaque)]
structure core.iter.adapters.chain.Chain (A : Type u) (B : Type v) where
  a : Option A
  b : Option B

@[rust_type "core::iter::adapters::cloned::Cloned" (body := .opaque)]
structure core.iter.adapters.cloned.Cloned (I : Type u) where
  it : I

@[rust_type "core::iter::adapters::copied::Copied" (body := .opaque)]
structure core.iter.adapters.copied.Copied (I : Type u) where
  it : I

/-! ## Provided `Iterator` methods -/

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::sum"]
def core.iter.traits.iterator.Iterator.sum.default
  {Self : Type} {S : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (accumSumInst : core.iter.traits.accum.Sum S Clause0_Item) : Self → Result S :=
  fun self => accumSumInst.sum IteratorInst self

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::cloned"]
def core.iter.traits.iterator.Iterator.cloned.default
  {Self : Type _} {T : Type _} {Clause2_Item : Type _}
  (_IteratorSelfSharedATInst : core.iter.traits.iterator.Iterator Self T)
  (_cloneCloneInst : core.clone.Clone T)
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause2_Item) :
  Self → Result (core.iter.adapters.cloned.Cloned Self) :=
  fun self => ok ⟨self⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::copied"]
def core.iter.traits.iterator.Iterator.copied.default
  {Self : Type _} {T : Type _} {Clause2_Item : Type _}
  (_IteratorSelfSharedATInst : core.iter.traits.iterator.Iterator Self T)
  (_markerCopyInst : core.marker.Copy T)
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause2_Item) :
  Self → Result (core.iter.adapters.copied.Copied Self) :=
  fun self => ok ⟨self⟩

/-- `min_by_key`: `self.map(|x| (f(&x), x)).min_by(|(a, _), (b, _)| a.cmp(b))`; keys are
    computed once per element in order, the first minimal element wins. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::min_by_key"]
def core.iter.traits.iterator.Iterator.min_by_key.default
  {Self : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (cmpOrdInst : core.cmp.Ord B)
  (opsfunctionFnMutFTupleSharedClause0_ItemBInst : core.ops.function.FnMut F Clause0_Item B) :
  Self → F → Result (Option Clause0_Item) :=
  fun self f => do
    let (o, it) ← IteratorInst.next self
    match o with
    | none => ok none
    | some x0 => do
      let (k0, f) ← opsfunctionFnMutFTupleSharedClause0_ItemBInst.call_mut f x0
      let (_, x, _) ← foldNext IteratorInst.next it (k0, x0, f) (fun (k, x, f) y => do
        let (ky, f) ← opsfunctionFnMutFTupleSharedClause0_ItemBInst.call_mut f y
        let c ← cmpOrdInst.cmp k ky
        if c = .gt then ok (ky, y, f) else ok (k, x, f))
      ok (some x)

/-- `max_by`: `reduce(|x, y| cmp::max_by(x, y, &mut compare))`; on `Equal` the later element
    wins. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::max_by"]
def core.iter.traits.iterator.Iterator.max_by.default
  {Self : Type _} {F : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairSharedClause0_ItemSharedClause0_ItemOrderingInst :
    core.ops.function.FnMut F (Clause0_Item × Clause0_Item) Ordering) :
  Self → F → Result (Option Clause0_Item) :=
  fun self f => do
    let (o, it) ← IteratorInst.next self
    match o with
    | none => ok none
    | some x0 => do
      let (x, _) ← foldNext IteratorInst.next it (x0, f) (fun (x, f) y => do
        let (c, f) ←
          opsfunctionFnMutFPairSharedClause0_ItemSharedClause0_ItemOrderingInst.call_mut f (x, y)
        if c = .gt then ok (x, f) else ok (y, f))
      ok (some x)

/-- `max`: `max_by(Ord::cmp)`. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::max"]
def core.iter.traits.iterator.Iterator.max.default
  {Self : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (cmpOrdInst : core.cmp.Ord Clause0_Item) : Self → Result (Option Clause0_Item) :=
  fun self => do
    let (o, it) ← IteratorInst.next self
    match o with
    | none => ok none
    | some x0 => do
      let x ← foldNext IteratorInst.next it x0 (fun x y => do
        let c ← cmpOrdInst.cmp x y
        if c = .gt then ok x else ok y)
      ok (some x)

/-- `ExactSizeIterator::len`: `size_hint` with `assert_eq!(upper, Some(lower))`. -/
@[trait_default, rust_fun "core::iter::traits::exact_size::ExactSizeIterator::len"]
def core.iter.traits.exact_size.ExactSizeIterator.len.default
  {Self : Type _} {Clause0_Clause0_Item : Type _}
  (ExactSizeIteratorInst : core.iter.traits.exact_size.ExactSizeIterator Self Clause0_Clause0_Item) :
  Self → Result Std.Usize :=
  fun self => lenOfHint (ExactSizeIteratorInst.iteratorInst.size_hint self)

/-- `rposition`: `let n = self.len(); self.try_rfold(n, |i, x| { let i = i - 1;
    if predicate(x) { Break(i) } else { Continue(i) } })`. The predicate sees the items from
    the back; the item values are read through the forward instance (the Lean signature has
    distinct item types for both directions), the iterator state advances through
    `next_back`. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::rposition"]
def core.iter.traits.iterator.Iterator.rposition.default
  {Self : Type _} {P : Type _} {Clause0_Item : Type _} {Clause2_Clause0_Item : Type _}
  {Clause3_Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutPTupleClause0_ItemBoolInst : core.ops.function.FnMut P Clause0_Item Bool)
  (exact_sizeExactSizeIteratorInst :
    core.iter.traits.exact_size.ExactSizeIterator Self Clause2_Clause0_Item)
  (double_endedDoubleEndedIteratorInst :
    core.iter.traits.double_ended.DoubleEndedIterator Self Clause3_Clause0_Item) :
  Self → P → Result ((Option Std.Usize) × Self) :=
  fun self p => do
    let n ← lenOfHint (exact_sizeExactSizeIteratorInst.iteratorInst.size_hint self)
    let xs ← toListNext IteratorInst.next self
    let it := self
    -- Walk from the back: `k` items examined so far.
    let (r, it) ← tryFoldNext (fun (st : List Clause0_Item × Self) => do
        match st.1 with
        | [] => do
          let (o, it) ← double_endedDoubleEndedIteratorInst.next_back st.2
          match o with
          | none => ok (none, ([], it))
          | some _ => ok (none, ([], it))
        | x :: rest => do
          let (_, it) ← double_endedDoubleEndedIteratorInst.next_back st.2
          ok (some x, (rest, it)))
      (xs.reverse, it) (n.val, p) (fun (i, p) x => do
        let i := i - 1
        let (b, p) ← opsfunctionFnMutPTupleClause0_ItemBoolInst.call_mut p x
        if b then ok (.inr i) else ok (.inl (i, p)))
    match r with
    | .inl _ => ok (none, it.2)
    | .inr i => ok (some (Usize.satOfNat i), it.2)

/-- `position`: `try_fold(0, |i, x| if predicate(x) { Break(i) } else { Continue(i + 1) })`. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::position"]
def core.iter.traits.iterator.Iterator.position.default
  {Self : Type _} {P : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutPTupleClause0_ItemBoolInst : core.ops.function.FnMut P Clause0_Item Bool) :
  Self → P → Result ((Option Std.Usize) × Self) :=
  fun self p => do
    let (r, it) ← tryFoldNext IteratorInst.next self (0#usize, p) (fun st x => do
      let (b, p1) ← opsfunctionFnMutPTupleClause0_ItemBoolInst.call_mut st.2 x
      if b then ok (.inr st.1) else do
        let i1 ← st.1 + 1#usize
        ok (.inl (i1, p1)))
    match r with
    | .inl _ => ok (none, it)
    | .inr i => ok (some i, it)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find_map"]
def core.iter.traits.iterator.Iterator.find_map.default
  {Self : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemOptionInst :
    core.ops.function.FnMut F Clause0_Item (Option B)) :
  Self → F → Result ((Option B) × Self) :=
  fun self f => do
    let (r, it, _) ← findMapNext IteratorInst.next
      opsfunctionFnMutFTupleClause0_ItemOptionInst.call_mut self f
    ok (r, it)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find"]
def core.iter.traits.iterator.Iterator.find.default
  {Self : Type _} {P : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  Self → P → Result ((Option Clause0_Item) × Self) :=
  fun self p => do
    let (r, it, _) ← findNext IteratorInst.next
      opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst.call_mut self p
    ok (r, it)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def core.iter.traits.iterator.Iterator.any.default
  {Self : Type _} {F : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBoolInst : core.ops.function.FnMut F Clause0_Item Bool) :
  Self → F → Result (Bool × Self) :=
  fun self f => do
    let (r, it) ← tryFoldNext IteratorInst.next self f (fun f x => do
      let (b, f) ← opsfunctionFnMutFTupleClause0_ItemBoolInst.call_mut f x
      if b then ok (.inr ()) else ok (.inl f))
    match r with
    | .inl _ => ok (false, it)
    | .inr _ => ok (true, it)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::all"]
def core.iter.traits.iterator.Iterator.all.default
  {Self : Type _} {F : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBoolInst : core.ops.function.FnMut F Clause0_Item Bool) :
  Self → F → Result (Bool × Self) :=
  fun self f => do
    let (r, it) ← tryFoldNext IteratorInst.next self f (fun f x => do
      let (b, f) ← opsfunctionFnMutFTupleClause0_ItemBoolInst.call_mut f x
      if b then ok (.inl f) else ok (.inr ()))
    match r with
    | .inl _ => ok (true, it)
    | .inr _ => ok (false, it)

/-- `by_ref`: a mutable borrow of the iterator. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::by_ref"]
def core.iter.traits.iterator.Iterator.by_ref.default
  {Self : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Result (Self × (Self → Self)) :=
  fun self => ok (self, fun s => s)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fuse"]
def core.iter.traits.iterator.Iterator.fuse.default
  {Self : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Result (core.iter.adapters.fuse.Fuse Self) :=
  fun self => ok ⟨some self⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flatten"]
def core.iter.traits.iterator.Iterator.flatten.default
  {Self : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _} {Clause1_IntoIter : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (_collectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator Clause0_Item Clause1_Item Clause1_IntoIter) :
  Self → Result (core.iter.adapters.flatten.Flatten Self Clause0_Item Clause1_Item
    Clause1_IntoIter) :=
  fun self => ok ⟨some self, none, none⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flat_map"]
def core.iter.traits.iterator.Iterator.flat_map.default
  {Self : Type _} {U : Type _} {F : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  {Clause1_IntoIter : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (_collectIntoIteratorInst : core.iter.traits.collect.IntoIterator U Clause1_Item Clause1_IntoIter)
  (_opsfunctionFnMutFTupleClause0_ItemUInst : core.ops.function.FnMut F Clause0_Item U) :
  Self → F → Result (core.iter.adapters.flatten.FlatMap Self U F Clause1_Item Clause1_IntoIter) :=
  fun self f => ok ⟨some (self, f), none, none⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::scan"]
def core.iter.traits.iterator.Iterator.scan.default
  {Self : Type _} {St : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (_opsfunctionFnMutFPairMutStClause0_ItemOptionInst :
    core.ops.function.FnMut F (St × Clause0_Item) (Option B)) :
  Self → St → F → Result (core.iter.adapters.scan.Scan Self St F) :=
  fun self st f => ok { iter := self, f, state := st }

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::skip"]
def core.iter.traits.iterator.Iterator.skip.default
  {Self : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Std.Usize → Result (core.iter.adapters.skip.Skip Self) :=
  fun self n => ok ⟨self, n⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::skip_while"]
def core.iter.traits.iterator.Iterator.skip_while.default
  {Self : Type _} {P : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (_opsfunctionFnMutPTupleSharedClause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  Self → P → Result (core.iter.adapters.skip_while.SkipWhile Self P) :=
  fun self p => ok ⟨self, false, p⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::peekable"]
def core.iter.traits.iterator.Iterator.peekable.default
  {Self : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Result (core.iter.adapters.peekable.Peekable Self Clause0_Item) :=
  fun self => ok ⟨self, none⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::filter_map"]
def core.iter.traits.iterator.Iterator.filter_map.default
  {Self : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (_opsfunctionFnMutFTupleClause0_ItemOptionInst :
    core.ops.function.FnMut F Clause0_Item (Option B)) :
  Self → F → Result (core.iter.adapters.filter_map.FilterMap Self F) :=
  fun self f => ok ⟨self, f⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::filter"]
def core.iter.traits.iterator.Iterator.filter.default
  {Self : Type _} {P : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (_opsfunctionFnMutPTupleSharedClause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  Self → P → Result (core.iter.adapters.filter.Filter Self P) :=
  fun self p => ok ⟨self, p⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.default
  {Self : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (_opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F Clause0_Item B) :
  Self → F → Result (core.iter.adapters.map.Map Self F) :=
  fun self f => ok ⟨self, f⟩

/-- `chain`: `Chain::new(self, other.into_iter())`. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::chain"]
def core.iter.traits.iterator.Iterator.chain.default
  {Self : Type _} {U : Type _} {Clause0_Item : Type _} {Clause1_IntoIter : Type _}
  (_IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (collectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator U Clause0_Item Clause1_IntoIter) :
  Self → U → Result (core.iter.adapters.chain.Chain Self Clause1_IntoIter) :=
  fun self other => do
    let b ← collectIntoIteratorInst.into_iter other
    ok ⟨some self, some b⟩

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::nth"]
def core.iter.traits.iterator.Iterator.nth.default
  {Self : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Std.Usize → Result ((Option Clause0_Item) × Self) :=
  fun self n => nthNext IteratorInst.next self n.val

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::last"]
def core.iter.traits.iterator.Iterator.last.default
  {Self : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Result (Option Clause0_Item) :=
  fun self => lastNext IteratorInst.next self

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::count"]
def core.iter.traits.iterator.Iterator.count.default
  {Self : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Result Std.Usize :=
  fun self => countNext IteratorInst.next self

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fold"]
def core.iter.traits.iterator.Iterator.fold.default
  {Self : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item) B) :
  Self → B → F → Result B :=
  fun self init f => do
    let (acc, _) ← foldNext IteratorInst.next self (init, f) (fun (acc, f) x =>
      opsfunctionFnMutFPairBInst.call_mut f (acc, x))
    ok acc

/-- `impl Sum for u32`: `iter.fold(0, |a, b| a + b)` (`+` with overflow checks). -/
@[rust_fun "core::iter::traits::accum::{core::iter::traits::accum::Sum<u32, u32>}::sum"]
def U32.Insts.CoreIterTraitsAccumSumU32.sum {I : Type _}
  (iteratorIteratorIU32Inst : core.iter.traits.iterator.Iterator I Std.U32) :
  I → Result Std.U32 :=
  fun it => foldNext iteratorIteratorIU32Inst.next it 0#u32 (fun a b => a + b)

/-! ## `Chain` -/

/-- `Chain::next`: `and_then_or_clear(&mut self.a, next).or_else(|| self.b.as_mut()?.next())`. -/
@[rust_fun
  "core::iter::adapters::chain::{core::iter::traits::iterator::Iterator<core::iter::adapters::chain::Chain<@A, @B>, @Clause0_Item>}::next"]
def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next
  {A : Type _} {B : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause0_Item) :
  core.iter.adapters.chain.Chain A B →
    Result ((Option Clause0_Item) × (core.iter.adapters.chain.Chain A B)) :=
  fun self => do
    let (r, a) ← andThenOrClear self.a traitsiteratorIteratorInst.next
    match r with
    | some x => ok (some x, ⟨a, self.b⟩)
    | none =>
      match self.b with
      | none => ok (none, ⟨a, none⟩)
      | some b => do
        let (r, b) ← traitsiteratorIteratorInst1.next b
        ok (r, ⟨a, some b⟩)

@[rust_fun
  "core::iter::adapters::chain::{core::iter::traits::iterator::Iterator<core::iter::adapters::chain::Chain<@A, @B>, @Clause0_Item>}::size_hint"]
def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.size_hint
  {A : Type _} {B : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause0_Item) :
  core.iter.adapters.chain.Chain A B → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    match self.a, self.b with
    | some a, some b => do
      let (alo, ahi) ← traitsiteratorIteratorInst.size_hint a
      let (blo, bhi) ← traitsiteratorIteratorInst1.size_hint b
      let lower := Usize.satOfNat (alo.val + blo.val)
      let upper := match ahi, bhi with
        | some x, some y => Usize.checkedOfNat (x.val + y.val)
        | _, _ => none
      ok (lower, upper)
    | some a, none => traitsiteratorIteratorInst.size_hint a
    | none, some b => traitsiteratorIteratorInst1.size_hint b
    | none, none => ok (0#usize, some 0#usize)

/-- `Chain::last`: `b_last.or(a_last)`, exhausting `a` first. -/
@[rust_fun
  "core::iter::adapters::chain::{core::iter::traits::iterator::Iterator<core::iter::adapters::chain::Chain<@A, @B>, @Clause0_Item>}::last"]
def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.last
  {A : Type _} {B : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause0_Item) :
  core.iter.adapters.chain.Chain A B → Result (Option Clause0_Item) :=
  fun self => do
    let aLast ← match self.a with
      | none => ok none
      | some a => lastNext traitsiteratorIteratorInst.next a
    let bLast ← match self.b with
      | none => ok none
      | some b => lastNext traitsiteratorIteratorInst1.next b
    ok (bLast.or aLast)

/-- `Chain::find`: `a.find(p)` (clearing `a` when exhausted), then `b.find(p)`. -/
@[rust_fun
  "core::iter::adapters::chain::{core::iter::traits::iterator::Iterator<core::iter::adapters::chain::Chain<@A, @B>, @Clause0_Item>}::find"]
def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.find
  {A : Type _} {B : Type _} {P : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause0_Item)
  (opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  core.iter.adapters.chain.Chain A B → P →
    Result ((Option Clause0_Item) × (core.iter.adapters.chain.Chain A B)) :=
  fun self p => do
    let call := opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst.call_mut
    let (ra, a, p) ← match self.a with
      | none => ok (none, none, p)
      | some a => do
        let (r, a, p) ← findNext traitsiteratorIteratorInst.next call a p
        match r with
        | none => ok (none, none, p)
        | some x => ok (some x, some a, p)
    match ra with
    | some x => ok (some x, ⟨a, self.b⟩)
    | none =>
      match self.b with
      | none => ok (none, ⟨a, none⟩)
      | some b => do
        let (r, b, _) ← findNext traitsiteratorIteratorInst1.next call b p
        ok (r, ⟨a, some b⟩)

/-- `Chain::nth`: `a.advance_by(n)` then `a.next()`, otherwise `b.nth(remaining)`. -/
@[rust_fun
  "core::iter::adapters::chain::{core::iter::traits::iterator::Iterator<core::iter::adapters::chain::Chain<@A, @B>, @Clause0_Item>}::nth"]
def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.nth
  {A : Type _} {B : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause0_Item) :
  core.iter.adapters.chain.Chain A B → Std.Usize →
    Result ((Option Clause0_Item) × (core.iter.adapters.chain.Chain A B)) :=
  fun self n => do
    let (found, n, a) ← match self.a with
      | none => ok (none, n.val, none)
      | some a => do
        let (k, a) ← advanceByNext traitsiteratorIteratorInst.next a n.val
        if k = 0 then do
          let (o, a) ← traitsiteratorIteratorInst.next a
          match o with
          | some x => ok (some x, 0, some a)
          | none => ok (none, 0, none)
        else ok (none, k, none)
    match found with
    | some x => ok (some x, ⟨a, self.b⟩)
    | none =>
      match self.b with
      | none => ok (none, ⟨a, none⟩)
      | some b => do
        let (r, b) ← nthNext traitsiteratorIteratorInst1.next b n
        ok (r, ⟨a, some b⟩)

@[rust_fun
  "core::iter::adapters::chain::{core::iter::traits::iterator::Iterator<core::iter::adapters::chain::Chain<@A, @B>, @Clause0_Item>}::fold"]
def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.fold
  {A : Type _} {B : Type _} {Acc : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause0_Item)
  (opsfunctionFnMutFPairAccInst : core.ops.function.FnMut F (Acc × Clause0_Item) Acc) :
  core.iter.adapters.chain.Chain A B → Acc → F → Result Acc :=
  fun self acc f => do
    let step := fun (s : Acc × F) x => opsfunctionFnMutFPairAccInst.call_mut s.2 (s.1, x)
    let s ← match self.a with
      | none => ok (acc, f)
      | some a => foldNext traitsiteratorIteratorInst.next a (acc, f) step
    let s ← match self.b with
      | none => ok s
      | some b => foldNext traitsiteratorIteratorInst1.next b s step
    ok s.1

@[rust_fun
  "core::iter::adapters::chain::{core::iter::traits::iterator::Iterator<core::iter::adapters::chain::Chain<@A, @B>, @Clause0_Item>}::count"]
def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.count
  {A : Type _} {B : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause0_Item) :
  core.iter.adapters.chain.Chain A B → Result Std.Usize :=
  fun self => do
    let ac ← match self.a with
      | none => ok 0#usize
      | some a => countNext traitsiteratorIteratorInst.next a
    let bc ← match self.b with
      | none => ok 0#usize
      | some b => countNext traitsiteratorIteratorInst1.next b
    ac + bc

/-! ## `Cloned` / `Copied` -/

@[rust_fun
  "core::iter::adapters::cloned::{core::iter::traits::iterator::Iterator<core::iter::adapters::cloned::Cloned<@I>, @T>}::next"]
def core.iter.adapters.cloned.Cloned.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {T : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (cloneCloneInst : core.clone.Clone T) :
  core.iter.adapters.cloned.Cloned I → Result ((Option T) × (core.iter.adapters.cloned.Cloned I)) :=
  fun self => do
    let (o, it) ← traitsiteratorIteratorISharedATInst.next self.it
    match o with
    | none => ok (none, ⟨it⟩)
    | some x => do
      let x ← cloneCloneInst.clone x
      ok (some x, ⟨it⟩)

@[rust_fun
  "core::iter::adapters::cloned::{core::iter::traits::iterator::Iterator<core::iter::adapters::cloned::Cloned<@I>, @T>}::size_hint"]
def core.iter.adapters.cloned.Cloned.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {T : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (_cloneCloneInst : core.clone.Clone T) :
  core.iter.adapters.cloned.Cloned I → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => traitsiteratorIteratorISharedATInst.size_hint self.it

@[rust_fun
  "core::iter::adapters::cloned::{core::iter::traits::iterator::Iterator<core::iter::adapters::cloned::Cloned<@I>, @T>}::fold"]
def core.iter.adapters.cloned.Cloned.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {T : Type _} {Acc : Type _} {F : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (cloneCloneInst : core.clone.Clone T)
  (opsfunctionFnMutFPairAccInst : core.ops.function.FnMut F (Acc × T) Acc) :
  core.iter.adapters.cloned.Cloned I → Acc → F → Result Acc :=
  fun self acc f => do
    let (acc, _) ← foldNext traitsiteratorIteratorISharedATInst.next self.it (acc, f)
      (fun (acc, f) x => do
        let x ← cloneCloneInst.clone x
        opsfunctionFnMutFPairAccInst.call_mut f (acc, x))
    ok acc

@[rust_fun
  "core::iter::adapters::copied::{core::iter::traits::iterator::Iterator<core::iter::adapters::copied::Copied<@I>, @T>}::next"]
def core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {T : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (_markerCopyInst : core.marker.Copy T) :
  core.iter.adapters.copied.Copied I → Result ((Option T) × (core.iter.adapters.copied.Copied I)) :=
  fun self => do
    let (o, it) ← traitsiteratorIteratorISharedATInst.next self.it
    ok (o, ⟨it⟩)

@[rust_fun
  "core::iter::adapters::copied::{core::iter::traits::iterator::Iterator<core::iter::adapters::copied::Copied<@I>, @T>}::size_hint"]
def core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {T : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (_markerCopyInst : core.marker.Copy T) :
  core.iter.adapters.copied.Copied I → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => traitsiteratorIteratorISharedATInst.size_hint self.it

@[rust_fun
  "core::iter::adapters::copied::{core::iter::traits::iterator::Iterator<core::iter::adapters::copied::Copied<@I>, @T>}::fold"]
def core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {T : Type _} {Acc : Type _} {F : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (_markerCopyInst : core.marker.Copy T)
  (opsfunctionFnMutFPairAccInst : core.ops.function.FnMut F (Acc × T) Acc) :
  core.iter.adapters.copied.Copied I → Acc → F → Result Acc :=
  fun self acc f => do
    let (acc, _) ← foldNext traitsiteratorIteratorISharedATInst.next self.it (acc, f)
      (fun (acc, f) x => opsfunctionFnMutFPairAccInst.call_mut f (acc, x))
    ok acc

@[rust_fun
  "core::iter::adapters::copied::{core::iter::traits::iterator::Iterator<core::iter::adapters::copied::Copied<@I>, @T>}::count"]
def core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.count
  {I : Type _} {T : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (_markerCopyInst : core.marker.Copy T) :
  core.iter.adapters.copied.Copied I → Result Std.Usize :=
  fun self => countNext traitsiteratorIteratorISharedATInst.next self.it

@[rust_fun
  "core::iter::adapters::copied::{core::iter::traits::iterator::Iterator<core::iter::adapters::copied::Copied<@I>, @T>}::last"]
def core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.last
  {I : Type _} {T : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (_markerCopyInst : core.marker.Copy T) :
  core.iter.adapters.copied.Copied I → Result (Option T) :=
  fun self => lastNext traitsiteratorIteratorISharedATInst.next self.it

@[rust_fun
  "core::iter::adapters::copied::{core::iter::traits::iterator::Iterator<core::iter::adapters::copied::Copied<@I>, @T>}::nth"]
def core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.nth
  {I : Type _} {T : Type _}
  (traitsiteratorIteratorISharedATInst : core.iter.traits.iterator.Iterator I T)
  (_markerCopyInst : core.marker.Copy T) :
  core.iter.adapters.copied.Copied I → Std.Usize →
    Result ((Option T) × (core.iter.adapters.copied.Copied I)) :=
  fun self n => do
    let (o, it) ← nthNext traitsiteratorIteratorISharedATInst.next self.it n.val
    ok (o, ⟨it⟩)

/-! ## `Enumerate` -/

/-- `Enumerate::fold`: `count` increments (overflow checked) after each call of `fold`. -/
@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::fold"]
def core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.fold
  {I : Type _} {Acc : Type _} {Fold : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFoldPairAccPairUsizeClause0_ItemAccInst :
    core.ops.function.FnMut Fold (Acc × (Std.Usize × Clause0_Item)) Acc) :
  core.iter.adapters.enumerate.Enumerate I → Acc → Fold → Result Acc :=
  fun self acc f => do
    let (acc, _, _) ← foldNext traitsiteratorIteratorInst.next self.iter (acc, self.count, f)
      (fun (acc, c, f) x => do
        let (acc, f) ←
          opsfunctionFnMutFoldPairAccPairUsizeClause0_ItemAccInst.call_mut f (acc, (c, x))
        let c ← c + 1#usize
        ok (acc, c, f))
    ok acc

@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::count"]
def core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.count
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.enumerate.Enumerate I → Result Std.Usize :=
  fun self => countNext traitsiteratorIteratorInst.next self.iter

/-- `Enumerate::nth`: `let a = self.iter.nth(n)?; let i = self.count + n;
    self.count = i + 1; Some((i, a))`. -/
@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::nth"]
def core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.nth
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.enumerate.Enumerate I → Std.Usize →
    Result ((Option (Std.Usize × Clause0_Item)) × (core.iter.adapters.enumerate.Enumerate I)) :=
  fun self n => do
    let (o, it) ← nthNext traitsiteratorIteratorInst.next self.iter n.val
    match o with
    | none => ok (none, { self with iter := it })
    | some a => do
      let i ← self.count + n
      let c ← i + 1#usize
      ok (some (i, a), { iter := it, count := c })

/-! ## `Filter` / `FilterMap` -/

/-- `Filter::next`: `self.iter.find(&mut self.predicate)`. -/
@[rust_fun
  "core::iter::adapters::filter::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter::Filter<@I, @P>, @Clause0_Item>}::next"]
def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {P : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  core.iter.adapters.filter.Filter I P →
    Result ((Option Clause0_Item) × (core.iter.adapters.filter.Filter I P)) :=
  fun self => do
    let (r, it, p) ← findNext traitsiteratorIteratorInst.next
      opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst.call_mut self.iter self.predicate
    ok (r, ⟨it, p⟩)

/-- `Filter::size_hint`: `(0, upper)`. -/
@[rust_fun
  "core::iter::adapters::filter::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter::Filter<@I, @P>, @Clause0_Item>}::size_hint"]
def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {P : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (_opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  core.iter.adapters.filter.Filter I P → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => do
    let (_, hi) ← traitsiteratorIteratorInst.size_hint self.iter
    ok (0#usize, hi)

/-- `Filter::count`: `self.iter.map(|x| predicate(&x) as usize).sum()`. -/
@[rust_fun
  "core::iter::adapters::filter::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter::Filter<@I, @P>, @Clause0_Item>}::count"]
def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.count
  {I : Type _} {P : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutPTupleSharedClause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  core.iter.adapters.filter.Filter I P → Result Std.Usize :=
  fun self => do
    let (c, _) ← foldNext traitsiteratorIteratorInst.next self.iter (0#usize, self.predicate)
      (fun (c, p) x => do
        let (b, p) ← opsfunctionFnMutPTupleSharedClause0_ItemBoolInst.call_mut p x
        let c ← if b then c + 1#usize else ok c
        ok (c, p))
    ok c

/-- `Filter::fold`: `self.iter.fold(init, |acc, x| if predicate(&x) { fold(acc, x) } else { acc })`. -/
@[rust_fun
  "core::iter::adapters::filter::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter::Filter<@I, @P>, @Clause0_Item>}::fold"]
def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {P : Type _} {Acc : Type _} {Fold : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutPTupleSharedClause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool)
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × Clause0_Item) Acc) :
  core.iter.adapters.filter.Filter I P → Acc → Fold → Result Acc :=
  fun self acc f => do
    let (acc, _, _) ← foldNext traitsiteratorIteratorInst.next self.iter (acc, self.predicate, f)
      (fun (acc, p, f) x => do
        let (b, p) ← opsfunctionFnMutPTupleSharedClause0_ItemBoolInst.call_mut p x
        if b then do
          let (acc, f) ← opsfunctionFnMutFoldPairAccInst.call_mut f (acc, x)
          ok (acc, p, f)
        else ok (acc, p, f))
    ok acc

/-- `FilterMap::next`: `self.iter.find_map(&mut self.f)`. -/
@[rust_fun
  "core::iter::adapters::filter_map::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter_map::FilterMap<@I, @F>, @B>}::next"]
def core.iter.adapters.filter_map.FilterMap.Insts.CoreIterTraitsIteratorIterator.next
  {B : Type _} {I : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemOptionInst :
    core.ops.function.FnMut F Clause0_Item (Option B)) :
  core.iter.adapters.filter_map.FilterMap I F →
    Result ((Option B) × (core.iter.adapters.filter_map.FilterMap I F)) :=
  fun self => do
    let (r, it, f) ← findMapNext traitsiteratorIteratorInst.next
      opsfunctionFnMutFTupleClause0_ItemOptionInst.call_mut self.iter self.f
    ok (r, ⟨it, f⟩)

@[rust_fun
  "core::iter::adapters::filter_map::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter_map::FilterMap<@I, @F>, @B>}::size_hint"]
def core.iter.adapters.filter_map.FilterMap.Insts.CoreIterTraitsIteratorIterator.size_hint
  {B : Type _} {I : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (_opsfunctionFnMutFTupleClause0_ItemOptionInst :
    core.ops.function.FnMut F Clause0_Item (Option B)) :
  core.iter.adapters.filter_map.FilterMap I F → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => do
    let (_, hi) ← traitsiteratorIteratorInst.size_hint self.iter
    ok (0#usize, hi)

@[rust_fun
  "core::iter::adapters::filter_map::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter_map::FilterMap<@I, @F>, @B>}::fold"]
def core.iter.adapters.filter_map.FilterMap.Insts.CoreIterTraitsIteratorIterator.fold
  {B : Type _} {I : Type _} {F : Type _} {Acc : Type _} {Fold : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemOptionInst :
    core.ops.function.FnMut F Clause0_Item (Option B))
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × B) Acc) :
  core.iter.adapters.filter_map.FilterMap I F → Acc → Fold → Result Acc :=
  fun self acc g => do
    let (acc, _, _) ← foldNext traitsiteratorIteratorInst.next self.iter (acc, self.f, g)
      (fun (acc, f, g) x => do
        let (o, f) ← opsfunctionFnMutFTupleClause0_ItemOptionInst.call_mut f x
        match o with
        | none => ok (acc, f, g)
        | some y => do
          let (acc, g) ← opsfunctionFnMutFoldPairAccInst.call_mut g (acc, y)
          ok (acc, f, g))
    ok acc

/-! ## `Map` -/

@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  {B : Type _} {I : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F Clause0_Item B) :
  core.iter.adapters.map.Map I F → Result ((Option B) × (core.iter.adapters.map.Map I F)) :=
  fun self => do
    let (o, it) ← traitsiteratorIteratorInst.next self.iter
    match o with
    | none => ok (none, ⟨it, self.f⟩)
    | some x => do
      let (y, f) ← opsfunctionFnMutFTupleClause0_ItemBInst.call_mut self.f x
      ok (some y, ⟨it, f⟩)

@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::double_ended::DoubleEndedIterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next_back"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
  {B : Type _} {I : Type _} {F : Type _} {Clause0_Clause0_Item : Type _}
  (traitsdouble_endedDoubleEndedIteratorInst :
    core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item)
  (opsfunctionFnMutFTupleClause0_Clause0_ItemBInst :
    core.ops.function.FnMut F Clause0_Clause0_Item B) :
  core.iter.adapters.map.Map I F → Result ((Option B) × (core.iter.adapters.map.Map I F)) :=
  fun self => do
    let (o, it) ← traitsdouble_endedDoubleEndedIteratorInst.next_back self.iter
    match o with
    | none => ok (none, ⟨it, self.f⟩)
    | some x => do
      let (y, f) ← opsfunctionFnMutFTupleClause0_Clause0_ItemBInst.call_mut self.f x
      ok (some y, ⟨it, f⟩)

@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::size_hint"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.size_hint
  {B : Type _} {I : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (_opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F Clause0_Item B) :
  core.iter.adapters.map.Map I F → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => traitsiteratorIteratorInst.size_hint self.iter

@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::fold"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.fold
  {B : Type _} {I : Type _} {F : Type _} {Acc : Type _} {G : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F Clause0_Item B)
  (opsfunctionFnMutGPairAccInst : core.ops.function.FnMut G (Acc × B) Acc) :
  core.iter.adapters.map.Map I F → Acc → G → Result Acc :=
  fun self acc g => do
    let (acc, _, _) ← foldNext traitsiteratorIteratorInst.next self.iter (acc, self.f, g)
      (fun (acc, f, g) x => do
        let (y, f) ← opsfunctionFnMutFTupleClause0_ItemBInst.call_mut f x
        let (acc, g) ← opsfunctionFnMutGPairAccInst.call_mut g (acc, y)
        ok (acc, f, g))
    ok acc

/-- `ExactSizeIterator for Map`: `self.iter.len()`. -/
@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::exact_size::ExactSizeIterator<core::iter::adapters::map::Map<@I, @F>, @B>}::len"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsExact_sizeExactSizeIterator.len
  {B : Type _} {I : Type _} {F : Type _} {Clause0_Clause0_Item : Type _}
  (traitsexact_sizeExactSizeIteratorInst :
    core.iter.traits.exact_size.ExactSizeIterator I Clause0_Clause0_Item)
  (_opsfunctionFnMutFTupleClause0_Clause0_ItemBInst :
    core.ops.function.FnMut F Clause0_Clause0_Item B) :
  core.iter.adapters.map.Map I F → Result Std.Usize :=
  fun self => lenOfHint (traitsexact_sizeExactSizeIteratorInst.iteratorInst.size_hint self.iter)

/-! ## `Fuse` -/

@[rust_fun
  "core::iter::adapters::fuse::{core::iter::traits::iterator::Iterator<core::iter::adapters::fuse::Fuse<@I>, @Clause0_Item>}::next"]
def core.iter.adapters.fuse.Fuse.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.fuse.Fuse I → Result ((Option Clause0_Item) × (core.iter.adapters.fuse.Fuse I)) :=
  fun self => do
    let (r, it) ← andThenOrClear self.iter traitsiteratorIteratorInst.next
    ok (r, ⟨it⟩)

/-! ## `Flatten` -/

/-- The fused outer iterator of `Flatten`, yielding inner iterators. -/
def core.iter.adapters.flatten.Flatten.outerNext
  {I : Type _} {U : Type _} {Clause0_Item : Type _} {Clause2_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator Clause0_Item Clause2_Item U) (i : I) :
  Result (Option U × I) := do
  let (o, i) ← traitsiteratorIteratorInst.next i
  match o with
  | none => ok (none, i)
  | some x => do
    let u ← traitscollectIntoIteratorInst.into_iter x
    ok (some u, i)

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>}::next"]
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {U : Type _} {Clause0_Item : Type _} {Clause2_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator Clause0_Item Clause2_Item U)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator U Clause2_Item) :
  core.iter.adapters.flatten.Flatten I Clause0_Item Clause2_Item U →
    Result ((Option Clause2_Item) × (core.iter.adapters.flatten.Flatten I Clause0_Item
      Clause2_Item U)) :=
  fun self => do
    let (r, outer, front, back) ← flatNext
      (core.iter.adapters.flatten.Flatten.outerNext traitsiteratorIteratorInst
        traitscollectIntoIteratorInst)
      traitsiteratorIteratorInst1.next self.iter self.frontiter self.backiter
    ok (r, ⟨outer, front, back⟩)

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>}::size_hint"]
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {U : Type _} {Clause0_Item : Type _} {Clause2_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (_traitscollectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator Clause0_Item Clause2_Item U)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator U Clause2_Item) :
  core.iter.adapters.flatten.Flatten I Clause0_Item Clause2_Item U →
    Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    flatSizeHint
      (match self.iter with
        | none => ok (0#usize, some 0#usize)
        | some i => traitsiteratorIteratorInst.size_hint i)
      traitsiteratorIteratorInst1.size_hint self.frontiter self.backiter

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>}::fold"]
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {U : Type _} {Acc : Type _} {Fold : Type _} {Clause0_Item : Type _}
  {Clause2_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator Clause0_Item Clause2_Item U)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator U Clause2_Item)
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × Clause2_Item) Acc) :
  core.iter.adapters.flatten.Flatten I Clause0_Item Clause2_Item U → Acc → Fold → Result Acc :=
  fun self acc f => do
    let (acc, _) ← flatIterFold
      (core.iter.adapters.flatten.Flatten.outerNext traitsiteratorIteratorInst
        traitscollectIntoIteratorInst)
      self.iter self.frontiter self.backiter (acc, f) (fun s u =>
        foldNext traitsiteratorIteratorInst1.next u s (fun (acc, f) x =>
          opsfunctionFnMutFoldPairAccInst.call_mut f (acc, x)))
    ok acc

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>}::count"]
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.count
  {I : Type _} {U : Type _} {Clause0_Item : Type _} {Clause2_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator Clause0_Item Clause2_Item U)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator U Clause2_Item) :
  core.iter.adapters.flatten.Flatten I Clause0_Item Clause2_Item U → Result Std.Usize :=
  fun self =>
    flatIterFold
      (core.iter.adapters.flatten.Flatten.outerNext traitsiteratorIteratorInst
        traitscollectIntoIteratorInst)
      self.iter self.frontiter self.backiter 0#usize (fun c u => do
        let n ← countNext traitsiteratorIteratorInst1.next u
        c + n)

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>}::last"]
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.last
  {I : Type _} {U : Type _} {Clause0_Item : Type _} {Clause2_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator Clause0_Item Clause2_Item U)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator U Clause2_Item) :
  core.iter.adapters.flatten.Flatten I Clause0_Item Clause2_Item U → Result (Option Clause2_Item) :=
  fun self =>
    flatIterFold
      (core.iter.adapters.flatten.Flatten.outerNext traitsiteratorIteratorInst
        traitscollectIntoIteratorInst)
      self.iter self.frontiter self.backiter none (fun l u => do
        let x ← lastNext traitsiteratorIteratorInst1.next u
        ok (x.or l))

/-! ## `FlatMap` -/

/-- The fused outer iterator of `FlatMap` (`Fuse<Map<I, F>>`), yielding inner iterators. -/
def core.iter.adapters.flatten.FlatMap.outerNext
  {I : Type _} {U : Type _} {F : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  {Clause1_IntoIter : Type _}
  (next : I → Result (Option Clause0_Item × I))
  (traitscollectIntoIteratorInst : core.iter.traits.collect.IntoIterator U Clause1_Item Clause1_IntoIter)
  (opsfunctionFnMutFTupleClause0_ItemUInst : core.ops.function.FnMut F Clause0_Item U)
  (s : I × F) : Result (Option Clause1_IntoIter × (I × F)) := do
  let (o, i) ← next s.1
  match o with
  | none => ok (none, (i, s.2))
  | some x => do
    let (u, f) ← opsfunctionFnMutFTupleClause0_ItemUInst.call_mut s.2 x
    let it ← traitscollectIntoIteratorInst.into_iter u
    ok (some it, (i, f))

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::FlatMap<@I, @U, @F, @Clause1_Item, @Clause1_IntoIter>, @Clause1_Item>}::next"]
def core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {U : Type _} {F : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  {Clause1_IntoIter : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst : core.iter.traits.collect.IntoIterator U Clause1_Item Clause1_IntoIter)
  (opsfunctionFnMutFTupleClause0_ItemUInst : core.ops.function.FnMut F Clause0_Item U) :
  core.iter.adapters.flatten.FlatMap I U F Clause1_Item Clause1_IntoIter →
    Result ((Option Clause1_Item) × (core.iter.adapters.flatten.FlatMap I U F Clause1_Item
      Clause1_IntoIter)) :=
  fun self => do
    let (r, outer, front, back) ← flatNext
      (core.iter.adapters.flatten.FlatMap.outerNext traitsiteratorIteratorInst.next
        traitscollectIntoIteratorInst opsfunctionFnMutFTupleClause0_ItemUInst)
      traitscollectIntoIteratorInst.iteratorInst.next self.iter self.frontiter self.backiter
    ok (r, ⟨outer, front, back⟩)

/-- `FlatMap::next_back`. The values of the inner items are read through the forward
    `IntoIterator` instance, the inner state advances with `next_back` (see
    `IterModel.backViaForward`). -/
@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::double_ended::DoubleEndedIterator<core::iter::adapters::flatten::FlatMap<@I, @U, @F, @Clause2_Item, @Clause2_IntoIter>, @Clause2_Item>}::next_back"]
def core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
  {I : Type _} {U : Type _} {F : Type _} {Clause0_Clause0_Item : Type _} {Clause2_Item : Type _}
  {Clause2_IntoIter : Type _} {Clause3_Clause0_Item : Type _}
  (traitsdouble_endedDoubleEndedIteratorInst :
    core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item)
  (opsfunctionFnMutFTupleClause0_Clause0_ItemUInst :
    core.ops.function.FnMut F Clause0_Clause0_Item U)
  (traitscollectIntoIteratorInst :
    core.iter.traits.collect.IntoIterator U Clause2_Item Clause2_IntoIter)
  (traitsdouble_endedDoubleEndedIteratorInst1 :
    core.iter.traits.double_ended.DoubleEndedIterator Clause2_IntoIter Clause3_Clause0_Item) :
  core.iter.adapters.flatten.FlatMap I U F Clause2_Item Clause2_IntoIter →
    Result ((Option Clause2_Item) × (core.iter.adapters.flatten.FlatMap I U F Clause2_Item
      Clause2_IntoIter)) :=
  fun self => do
    let (r, outer, front, back) ← flatNextBack
      (core.iter.adapters.flatten.FlatMap.outerNext traitsdouble_endedDoubleEndedIteratorInst.next_back
        traitscollectIntoIteratorInst opsfunctionFnMutFTupleClause0_Clause0_ItemUInst)
      (backViaForward traitscollectIntoIteratorInst.iteratorInst.next
        traitsdouble_endedDoubleEndedIteratorInst1.next_back)
      self.iter self.frontiter self.backiter
    ok (r, ⟨outer, front, back⟩)

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::FlatMap<@I, @U, @F, @Clause1_Item, @Clause1_IntoIter>, @Clause1_Item>}::size_hint"]
def core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {U : Type _} {F : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  {Clause1_IntoIter : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst : core.iter.traits.collect.IntoIterator U Clause1_Item Clause1_IntoIter)
  (_opsfunctionFnMutFTupleClause0_ItemUInst : core.ops.function.FnMut F Clause0_Item U) :
  core.iter.adapters.flatten.FlatMap I U F Clause1_Item Clause1_IntoIter →
    Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    flatSizeHint
      (match self.iter with
        | none => ok (0#usize, some 0#usize)
        | some (i, _) => traitsiteratorIteratorInst.size_hint i)
      traitscollectIntoIteratorInst.iteratorInst.size_hint self.frontiter self.backiter

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::FlatMap<@I, @U, @F, @Clause1_Item, @Clause1_IntoIter>, @Clause1_Item>}::fold"]
def core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {U : Type _} {F : Type _} {Acc : Type _} {Fold : Type _} {Clause0_Item : Type _}
  {Clause1_Item : Type _} {Clause1_IntoIter : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst : core.iter.traits.collect.IntoIterator U Clause1_Item Clause1_IntoIter)
  (opsfunctionFnMutFTupleClause0_ItemUInst : core.ops.function.FnMut F Clause0_Item U)
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × Clause1_Item) Acc) :
  core.iter.adapters.flatten.FlatMap I U F Clause1_Item Clause1_IntoIter → Acc → Fold → Result Acc :=
  fun self acc g => do
    let (acc, _) ← flatIterFold
      (core.iter.adapters.flatten.FlatMap.outerNext traitsiteratorIteratorInst.next
        traitscollectIntoIteratorInst opsfunctionFnMutFTupleClause0_ItemUInst)
      self.iter self.frontiter self.backiter (acc, g) (fun s u =>
        foldNext traitscollectIntoIteratorInst.iteratorInst.next u s (fun (acc, g) x =>
          opsfunctionFnMutFoldPairAccInst.call_mut g (acc, x)))
    ok acc

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::FlatMap<@I, @U, @F, @Clause1_Item, @Clause1_IntoIter>, @Clause1_Item>}::count"]
def core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator.count
  {I : Type _} {U : Type _} {F : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  {Clause1_IntoIter : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst : core.iter.traits.collect.IntoIterator U Clause1_Item Clause1_IntoIter)
  (opsfunctionFnMutFTupleClause0_ItemUInst : core.ops.function.FnMut F Clause0_Item U) :
  core.iter.adapters.flatten.FlatMap I U F Clause1_Item Clause1_IntoIter → Result Std.Usize :=
  fun self =>
    flatIterFold
      (core.iter.adapters.flatten.FlatMap.outerNext traitsiteratorIteratorInst.next
        traitscollectIntoIteratorInst opsfunctionFnMutFTupleClause0_ItemUInst)
      self.iter self.frontiter self.backiter 0#usize (fun c u => do
        let n ← countNext traitscollectIntoIteratorInst.iteratorInst.next u
        c + n)

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::FlatMap<@I, @U, @F, @Clause1_Item, @Clause1_IntoIter>, @Clause1_Item>}::last"]
def core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator.last
  {I : Type _} {U : Type _} {F : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  {Clause1_IntoIter : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (traitscollectIntoIteratorInst : core.iter.traits.collect.IntoIterator U Clause1_Item Clause1_IntoIter)
  (opsfunctionFnMutFTupleClause0_ItemUInst : core.ops.function.FnMut F Clause0_Item U) :
  core.iter.adapters.flatten.FlatMap I U F Clause1_Item Clause1_IntoIter →
    Result (Option Clause1_Item) :=
  fun self =>
    flatIterFold
      (core.iter.adapters.flatten.FlatMap.outerNext traitsiteratorIteratorInst.next
        traitscollectIntoIteratorInst opsfunctionFnMutFTupleClause0_ItemUInst)
      self.iter self.frontiter self.backiter none (fun l u => do
        let x ← lastNext traitscollectIntoIteratorInst.iteratorInst.next u
        ok (x.or l))

/-! ## `Peekable` -/

/-- `Peekable::next`: `match self.peeked.take() { Some(v) => v, None => self.iter.next() }`. -/
@[rust_fun
  "core::iter::adapters::peekable::{core::iter::traits::iterator::Iterator<core::iter::adapters::peekable::Peekable<@I, @Clause0_Item>, @Clause0_Item>}::next"]
def core.iter.adapters.peekable.Peekable.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.peekable.Peekable I Clause0_Item →
    Result ((Option Clause0_Item) × (core.iter.adapters.peekable.Peekable I Clause0_Item)) :=
  fun self =>
    match self.peeked with
    | some v => ok (v, ⟨self.iter, none⟩)
    | none => do
      let (o, it) ← traitsiteratorIteratorInst.next self.iter
      ok (o, ⟨it, none⟩)

/-- `Peekable::peek`: `self.peeked.get_or_insert_with(|| iter.next()).as_ref()`. -/
@[rust_fun
  "core::iter::adapters::peekable::{core::iter::adapters::peekable::Peekable<@I, @Clause0_Item>}::peek"]
def core.iter.adapters.peekable.Peekable.peek
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.peekable.Peekable I Clause0_Item →
    Result ((Option Clause0_Item) × (core.iter.adapters.peekable.Peekable I Clause0_Item)) :=
  fun self =>
    match self.peeked with
    | some v => ok (v, self)
    | none => do
      let (o, it) ← traitsiteratorIteratorInst.next self.iter
      ok (o, ⟨it, some o⟩)

@[rust_fun
  "core::iter::adapters::peekable::{core::iter::traits::iterator::Iterator<core::iter::adapters::peekable::Peekable<@I, @Clause0_Item>, @Clause0_Item>}::count"]
def core.iter.adapters.peekable.Peekable.Insts.CoreIterTraitsIteratorIterator.count
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.peekable.Peekable I Clause0_Item → Result Std.Usize :=
  fun self =>
    match self.peeked with
    | some none => ok 0#usize
    | some (some _) => do
      let c ← countNext traitsiteratorIteratorInst.next self.iter
      1#usize + c
    | none => countNext traitsiteratorIteratorInst.next self.iter

/-- `Peekable::nth`. -/
@[rust_fun
  "core::iter::adapters::peekable::{core::iter::traits::iterator::Iterator<core::iter::adapters::peekable::Peekable<@I, @Clause0_Item>, @Clause0_Item>}::nth"]
def core.iter.adapters.peekable.Peekable.Insts.CoreIterTraitsIteratorIterator.nth
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.peekable.Peekable I Clause0_Item → Std.Usize →
    Result ((Option Clause0_Item) × (core.iter.adapters.peekable.Peekable I Clause0_Item)) :=
  fun self n =>
    match self.peeked with
    | some none => ok (none, ⟨self.iter, none⟩)
    | some (some v) =>
      if n.val = 0 then ok (some v, ⟨self.iter, none⟩)
      else do
        let (o, it) ← nthNext traitsiteratorIteratorInst.next self.iter (n.val - 1)
        ok (o, ⟨it, none⟩)
    | none => do
      let (o, it) ← nthNext traitsiteratorIteratorInst.next self.iter n.val
      ok (o, ⟨it, none⟩)

/-- `Peekable::last`: `self.iter.last().or(peek_opt)`. -/
@[rust_fun
  "core::iter::adapters::peekable::{core::iter::traits::iterator::Iterator<core::iter::adapters::peekable::Peekable<@I, @Clause0_Item>, @Clause0_Item>}::last"]
def core.iter.adapters.peekable.Peekable.Insts.CoreIterTraitsIteratorIterator.last
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.peekable.Peekable I Clause0_Item → Result (Option Clause0_Item) :=
  fun self =>
    match self.peeked with
    | some none => ok none
    | some (some v) => do
      let l ← lastNext traitsiteratorIteratorInst.next self.iter
      ok (l.or (some v))
    | none => lastNext traitsiteratorIteratorInst.next self.iter

/-- `Peekable::size_hint`. -/
@[rust_fun
  "core::iter::adapters::peekable::{core::iter::traits::iterator::Iterator<core::iter::adapters::peekable::Peekable<@I, @Clause0_Item>, @Clause0_Item>}::size_hint"]
def core.iter.adapters.peekable.Peekable.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.peekable.Peekable I Clause0_Item → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    match self.peeked with
    | some none => ok (0#usize, some 0#usize)
    | p => do
      let peekLen := match p with
        | some (some _) => 1
        | _ => 0
      let (lo, hi) ← traitsiteratorIteratorInst.size_hint self.iter
      ok (Usize.satOfNat (lo.val + peekLen), hi.bind fun h => Usize.checkedOfNat (h.val + peekLen))

/-- `Peekable::fold`. -/
@[rust_fun
  "core::iter::adapters::peekable::{core::iter::traits::iterator::Iterator<core::iter::adapters::peekable::Peekable<@I, @Clause0_Item>, @Clause0_Item>}::fold"]
def core.iter.adapters.peekable.Peekable.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {Acc : Type _} {Fold : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × Clause0_Item) Acc) :
  core.iter.adapters.peekable.Peekable I Clause0_Item → Acc → Fold → Result Acc :=
  fun self acc f =>
    match self.peeked with
    | some none => ok acc
    | p => do
      let (acc, f) ← match p with
        | some (some v) => opsfunctionFnMutFoldPairAccInst.call_mut f (acc, v)
        | _ => ok (acc, f)
      let (acc, _) ← foldNext traitsiteratorIteratorInst.next self.iter (acc, f)
        (fun (acc, f) x => opsfunctionFnMutFoldPairAccInst.call_mut f (acc, x))
      ok acc

/-! ## `Rev` -/

@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::size_hint"]
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {Clause0_Clause0_Item : Type _}
  (traitsdouble_endedDoubleEndedIteratorInst :
    core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item) :
  core.iter.adapters.rev.Rev I → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => traitsdouble_endedDoubleEndedIteratorInst.iteratorInst.size_hint self.iter

/-- `Rev::nth`: `self.iter.nth_back(n)`. -/
@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::nth"]
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.nth
  {I : Type _} {Clause0_Clause0_Item : Type _}
  (traitsdouble_endedDoubleEndedIteratorInst :
    core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item) :
  core.iter.adapters.rev.Rev I → Std.Usize →
    Result ((Option Clause0_Clause0_Item) × (core.iter.adapters.rev.Rev I)) :=
  fun self n => do
    let (o, it) ← nthNext traitsdouble_endedDoubleEndedIteratorInst.next_back self.iter n.val
    ok (o, ⟨it⟩)

/-- `Rev::fold`: `self.iter.rfold(init, f)`. -/
@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::fold"]
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {Acc : Type _} {F : Type _} {Clause0_Clause0_Item : Type _}
  (traitsdouble_endedDoubleEndedIteratorInst :
    core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item)
  (opsfunctionFnMutFPairAccInst : core.ops.function.FnMut F (Acc × Clause0_Clause0_Item) Acc) :
  core.iter.adapters.rev.Rev I → Acc → F → Result Acc :=
  fun self acc f => do
    let (acc, _) ← foldNext traitsdouble_endedDoubleEndedIteratorInst.next_back self.iter (acc, f)
      (fun (acc, f) x => opsfunctionFnMutFPairAccInst.call_mut f (acc, x))
    ok acc

/-- `Rev::find`: `self.iter.rfind(predicate)`. -/
@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::find"]
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.find
  {I : Type _} {P : Type _} {Clause0_Clause0_Item : Type _}
  (traitsdouble_endedDoubleEndedIteratorInst :
    core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item)
  (opsfunctionFnMutPTupleShared0Clause0_Clause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Clause0_Item Bool) :
  core.iter.adapters.rev.Rev I → P →
    Result ((Option Clause0_Clause0_Item) × (core.iter.adapters.rev.Rev I)) :=
  fun self p => do
    let (r, it, _) ← findNext traitsdouble_endedDoubleEndedIteratorInst.next_back
      opsfunctionFnMutPTupleShared0Clause0_Clause0_ItemBoolInst.call_mut self.iter p
    ok (r, ⟨it⟩)

/-! ## `Scan` -/

/-- `Scan::next`: `let a = self.iter.next()?; (self.f)(&mut self.state, a)`.

    The closure receives `(state, item)`. The `FnMut` model returns only the closure output
    and the closure's own new state, so updates the closure makes through its `&mut St`
    argument are not observable here: `state` is passed unchanged to every call. -/
@[rust_fun
  "core::iter::adapters::scan::{core::iter::traits::iterator::Iterator<core::iter::adapters::scan::Scan<@I, @St, @F>, @B>}::next"]
def core.iter.adapters.scan.Scan.Insts.CoreIterTraitsIteratorIterator.next
  {B : Type _} {I : Type _} {St : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFPairMut0StClause0_ItemOptionInst :
    core.ops.function.FnMut F (St × Clause0_Item) (Option B)) :
  core.iter.adapters.scan.Scan I St F →
    Result ((Option B) × (core.iter.adapters.scan.Scan I St F)) :=
  fun self => do
    let (o, it) ← traitsiteratorIteratorInst.next self.iter
    match o with
    | none => ok (none, { self with iter := it })
    | some a => do
      let (r, f) ← opsfunctionFnMutFPairMut0StClause0_ItemOptionInst.call_mut self.f (self.state, a)
      ok (r, { iter := it, f, state := self.state })

/-- `Scan::size_hint`: `(0, upper)`. -/
@[rust_fun
  "core::iter::adapters::scan::{core::iter::traits::iterator::Iterator<core::iter::adapters::scan::Scan<@I, @St, @F>, @B>}::size_hint"]
def core.iter.adapters.scan.Scan.Insts.CoreIterTraitsIteratorIterator.size_hint
  {B : Type _} {I : Type _} {St : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (_opsfunctionFnMutFPairMut0StClause0_ItemOptionInst :
    core.ops.function.FnMut F (St × Clause0_Item) (Option B)) :
  core.iter.adapters.scan.Scan I St F → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => do
    let (_, hi) ← traitsiteratorIteratorInst.size_hint self.iter
    ok (0#usize, hi)

/-- `Scan::fold`: the provided `fold` (through `try_fold`): stops at the first `None` of the
    scan closure. -/
@[rust_fun
  "core::iter::adapters::scan::{core::iter::traits::iterator::Iterator<core::iter::adapters::scan::Scan<@I, @St, @F>, @B>}::fold"]
def core.iter.adapters.scan.Scan.Insts.CoreIterTraitsIteratorIterator.fold
  {B : Type _} {I : Type _} {St : Type _} {F : Type _} {AAA : Type _} {FFF : Type _}
  {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFPairMutStClause0_ItemOptionInst :
    core.ops.function.FnMut F (St × Clause0_Item) (Option B))
  (opsfunctionFnMutFFFPairAAAInst : core.ops.function.FnMut FFF (AAA × B) AAA) :
  core.iter.adapters.scan.Scan I St F → AAA → FFF → Result AAA :=
  fun self acc g => do
    let (r, _) ← tryFoldNext traitsiteratorIteratorInst.next self.iter (acc, self.f, g)
      (fun (acc, f, g) x => do
        let (o, f) ← opsfunctionFnMutFPairMutStClause0_ItemOptionInst.call_mut f (self.state, x)
        match o with
        | none => ok (.inr acc)
        | some y => do
          let (acc, g) ← opsfunctionFnMutFFFPairAAAInst.call_mut g (acc, y)
          ok (.inl (acc, f, g)))
    match r with
    | .inl (acc, _, _) => ok acc
    | .inr acc => ok acc

/-! ## `Skip` -/

/-- `Skip::next`: `if self.n > 0 { self.iter.nth(mem::take(&mut self.n)) } else { self.iter.next() }`. -/
@[rust_fun
  "core::iter::adapters::skip::{core::iter::traits::iterator::Iterator<core::iter::adapters::skip::Skip<@I>, @Clause0_Item>}::next"]
def core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.skip.Skip I →
    Result ((Option Clause0_Item) × (core.iter.adapters.skip.Skip I)) :=
  fun self => do
    let (o, it) ← nthNext traitsiteratorIteratorInst.next self.iter self.n.val
    ok (o, ⟨it, 0#usize⟩)

/-- `Skip::nth`. -/
@[rust_fun
  "core::iter::adapters::skip::{core::iter::traits::iterator::Iterator<core::iter::adapters::skip::Skip<@I>, @Clause0_Item>}::nth"]
def core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.nth
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.skip.Skip I → Std.Usize →
    Result ((Option Clause0_Item) × (core.iter.adapters.skip.Skip I)) :=
  fun self n => do
    let next := traitsiteratorIteratorInst.next
    if self.n.val > 0 then
      let skip := self.n.val
      if skip + n.val ≤ Usize.max then do
        let (o, it) ← nthNext next self.iter (skip + n.val)
        ok (o, ⟨it, 0#usize⟩)
      else do
        -- `self.iter.nth(skip - 1)?; self.iter.nth(n)`
        let (o, it) ← nthNext next self.iter (skip - 1)
        match o with
        | none => ok (none, ⟨it, 0#usize⟩)
        | some _ => do
          let (o, it) ← nthNext next it n.val
          ok (o, ⟨it, 0#usize⟩)
    else do
      let (o, it) ← nthNext next self.iter n.val
      ok (o, ⟨it, self.n⟩)

@[rust_fun
  "core::iter::adapters::skip::{core::iter::traits::iterator::Iterator<core::iter::adapters::skip::Skip<@I>, @Clause0_Item>}::size_hint"]
def core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.skip.Skip I → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => do
    let (lo, hi) ← traitsiteratorIteratorInst.size_hint self.iter
    ok (Usize.satOfNat (lo.val - self.n.val), hi.map fun h => Usize.satOfNat (h.val - self.n.val))

/-- `Skip::count`: `if self.n > 0 { if self.iter.nth(self.n - 1).is_none() { return 0 } }
    self.iter.count()`. -/
@[rust_fun
  "core::iter::adapters::skip::{core::iter::traits::iterator::Iterator<core::iter::adapters::skip::Skip<@I>, @Clause0_Item>}::count"]
def core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.count
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.skip.Skip I → Result Std.Usize :=
  fun self => do
    let next := traitsiteratorIteratorInst.next
    if self.n.val > 0 then do
      let (o, it) ← nthNext next self.iter (self.n.val - 1)
      match o with
      | none => ok 0#usize
      | some _ => countNext next it
    else countNext next self.iter

@[rust_fun
  "core::iter::adapters::skip::{core::iter::traits::iterator::Iterator<core::iter::adapters::skip::Skip<@I>, @Clause0_Item>}::last"]
def core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.last
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.skip.Skip I → Result (Option Clause0_Item) :=
  fun self => do
    let next := traitsiteratorIteratorInst.next
    if self.n.val > 0 then do
      let (o, it) ← nthNext next self.iter (self.n.val - 1)
      match o with
      | none => ok none
      | some _ => lastNext next it
    else lastNext next self.iter

@[rust_fun
  "core::iter::adapters::skip::{core::iter::traits::iterator::Iterator<core::iter::adapters::skip::Skip<@I>, @Clause0_Item>}::fold"]
def core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {Acc : Type _} {Fold : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × Clause0_Item) Acc) :
  core.iter.adapters.skip.Skip I → Acc → Fold → Result Acc :=
  fun self acc f => do
    let next := traitsiteratorIteratorInst.next
    let go := fun (it : I) => do
      let (acc, _) ← foldNext next it (acc, f)
        (fun (acc, f) x => opsfunctionFnMutFoldPairAccInst.call_mut f (acc, x))
      ok acc
    if self.n.val > 0 then do
      let (o, it) ← nthNext next self.iter (self.n.val - 1)
      match o with
      | none => ok acc
      | some _ => go it
    else go self.iter

/-! ## `SkipWhile` -/

/-- `SkipWhile::next`: `self.iter.find(|x| if flag || !pred(x) { flag = true; true } else { false })`. -/
@[rust_fun
  "core::iter::adapters::skip_while::{core::iter::traits::iterator::Iterator<core::iter::adapters::skip_while::SkipWhile<@I, @P>, @Clause0_Item>}::next"]
def core.iter.adapters.skip_while.SkipWhile.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type _} {P : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  core.iter.adapters.skip_while.SkipWhile I P →
    Result ((Option Clause0_Item) × (core.iter.adapters.skip_while.SkipWhile I P)) :=
  fun self => do
    let (r, it, (flag, p)) ← findNext traitsiteratorIteratorInst.next
      (fun (st : Bool × P) x =>
        if st.1 then ok (true, st)
        else do
          let (b, p) ← opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst.call_mut st.2 x
          if b then ok (false, (false, p)) else ok (true, (true, p)))
      self.iter (self.flag, self.predicate)
    ok (r, ⟨it, flag, p⟩)

/-! ## `Take` / `TakeWhile` -/

/-- `Take::nth`. -/
@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::nth"]
def core.iter.adapters.take.Take.Insts.CoreIterTraitsIteratorIterator.nth
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.take.Take I → Std.Usize →
    Result ((Option Clause0_Item) × (core.iter.adapters.take.Take I)) :=
  fun self n => do
    let next := traitsiteratorIteratorInst.next
    if self.n.val > n.val then do
      let (o, it) ← nthNext next self.iter n.val
      ok (o, ⟨it, Usize.satOfNat (self.n.val - (n.val + 1))⟩)
    else if self.n.val > 0 then do
      let (_, it) ← nthNext next self.iter (self.n.val - 1)
      ok (none, ⟨it, 0#usize⟩)
    else ok (none, self)

/-- `Take::count`: the provided `count` (`fold` through `try_fold`, which stops right after
    the `n`-th element). -/
@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::count"]
def core.iter.adapters.take.Take.Insts.CoreIterTraitsIteratorIterator.count
  {I : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.take.Take I → Result Std.Usize :=
  fun self =>
    countNext (core.iter.adapters.take.IteratorTake.next traitsiteratorIteratorInst) self

/-- `Take::fold`: `try_fold` stopping after the `n`-th element (no extra `next` call). -/
@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::fold"]
def core.iter.adapters.take.Take.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item) B) :
  core.iter.adapters.take.Take I → B → F → Result B :=
  fun self acc f => do
    let (acc, _) ← foldNext (core.iter.adapters.take.IteratorTake.next traitsiteratorIteratorInst)
      self (acc, f) (fun (acc, f) x => opsfunctionFnMutFPairBInst.call_mut f (acc, x))
    ok acc

/-- `TakeWhile::size_hint`: `(0, Some(0))` once done, else `(0, upper)`. -/
@[rust_fun
  "core::iter::adapters::take_while::{core::iter::traits::iterator::Iterator<core::iter::adapters::take_while::TakeWhile<@I, @P>, @Clause0_Item>}::size_hint"]
def core.iter.adapters.take_while.TakeWhile.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type _} {P : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (_opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool) :
  core.iter.adapters.take_while.TakeWhile I P → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    if self.flag then ok (0#usize, some 0#usize)
    else do
      let (_, hi) ← traitsiteratorIteratorInst.size_hint self.iter
      ok (0#usize, hi)

/-- `TakeWhile::fold`: `try_fold` stopping at the first element failing the predicate. -/
@[rust_fun
  "core::iter::adapters::take_while::{core::iter::traits::iterator::Iterator<core::iter::adapters::take_while::TakeWhile<@I, @P>, @Clause0_Item>}::fold"]
def core.iter.adapters.take_while.TakeWhile.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type _} {P : Type _} {AAA : Type _} {FFF : Type _} {Clause0_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutPTupleSharedClause0_ItemBoolInst :
    core.ops.function.FnMut P Clause0_Item Bool)
  (opsfunctionFnMutFFFPairAAAInst : core.ops.function.FnMut FFF (AAA × Clause0_Item) AAA) :
  core.iter.adapters.take_while.TakeWhile I P → AAA → FFF → Result AAA :=
  fun self acc g =>
    if self.flag then ok acc
    else do
      let (r, _) ← tryFoldNext traitsiteratorIteratorInst.next self.iter (acc, self.predicate, g)
        (fun (acc, p, g) x => do
          let (b, p) ← opsfunctionFnMutPTupleSharedClause0_ItemBoolInst.call_mut p x
          if b then do
            let (acc, g) ← opsfunctionFnMutFFFPairAAAInst.call_mut g (acc, x)
            ok (.inl (acc, p, g))
          else ok (.inr acc))
      match r with
      | .inl (acc, _, _) => ok acc
      | .inr acc => ok acc

/-! ## `Zip` -/

/-- `Zip::size_hint` (`ZipImpl::size_hint`). -/
@[rust_fun
  "core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>}::size_hint"]
def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.size_hint
  {A : Type _} {B : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause1_Item) :
  core.iter.adapters.zip.Zip A B → Result (Std.Usize × (Option Std.Usize)) :=
  fun self => do
    let (alo, ahi) ← traitsiteratorIteratorInst.size_hint self.fst
    let (blo, bhi) ← traitsiteratorIteratorInst1.size_hint self.snd
    let lower := if alo.val ≤ blo.val then alo else blo
    let upper := match ahi, bhi with
      | some x, some y => some (if x.val ≤ y.val then x else y)
      | some x, none => some x
      | none, some y => some y
      | none, none => none
    ok (lower, upper)

/-- `Zip::nth` (`super_nth`): `next` until the `n`-th pair. -/
@[rust_fun
  "core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>}::nth"]
def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.nth
  {A : Type _} {B : Type _} {Clause0_Item : Type _} {Clause1_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause1_Item) :
  core.iter.adapters.zip.Zip A B → Std.Usize →
    Result ((Option (Clause0_Item × Clause1_Item)) × (core.iter.adapters.zip.Zip A B)) :=
  fun self n =>
    nthNext (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      traitsiteratorIteratorInst traitsiteratorIteratorInst1) self n.val

@[rust_fun
  "core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>}::fold"]
def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.fold
  {A : Type _} {B : Type _} {Acc : Type _} {F : Type _} {Clause0_Item : Type _}
  {Clause1_Item : Type _}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B Clause1_Item)
  (opsfunctionFnMutFPairAccPairAccInst :
    core.ops.function.FnMut F (Acc × (Clause0_Item × Clause1_Item)) Acc) :
  core.iter.adapters.zip.Zip A B → Acc → F → Result Acc :=
  fun self acc f => do
    let (acc, _) ← foldNext (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      traitsiteratorIteratorInst traitsiteratorIteratorInst1) self (acc, f)
      (fun (acc, f) x => opsfunctionFnMutFPairAccPairAccInst.call_mut f (acc, x))
    ok acc

end Aeneas.Std
