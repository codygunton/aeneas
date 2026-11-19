/- `alloc::collections::btree::set`: `BTreeSet` as its sorted list of elements (see
`BTreeMap.lean` for the conventions). `Difference` reproduces Rust's three strategies
(`Stitch`, `Search`, `Iterate`) since they are observable through `size_hint`. -/
module
public import Aeneas.Std.Alloc.Collections.BTreeMap
public section

namespace Aeneas.Std

open Result

@[rust_type "alloc::collections::btree::set::BTreeSet" (body := .opaque)]
structure alloc.collections.btree.set.BTreeSet (T : Type u) (A : Type v) where
  root : Bool
  elems : List T

namespace BTreeSetModel

/-- `DifferenceInner`: remaining elements of `self` (and of `other` for `stitch`, the whole of
    `other` for `search`). -/
inductive DifferenceInner (T : Type u) where
| stitch (selfRest otherRest : List T)
| search (selfRest other : List T)
| iterate (selfRest : List T)

/-- Membership by binary-tree search order (`key.cmp(k)`). -/
@[expose] def contains {T : Type u} (ordT : core.cmp.Ord T) (x : T) (l : List T) : Result Bool := do
  let (_, found) ← BTreeMapModel.search (V := Unit) ordT.cmp x (l.map fun y => (y, ()))
  ok found

end BTreeSetModel

@[rust_type "alloc::collections::btree::set::Difference" (body := .opaque)]
structure alloc.collections.btree.set.Difference (T : Type u) (A : Type v) where
  inner : BTreeSetModel.DifferenceInner T

open BTreeSetModel

@[expose, rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, alloc::alloc::Global>}::new"]
def alloc.collections.btree.set.BTreeSetTGlobal.new (T : Type _) :
    Result (alloc.collections.btree.set.BTreeSet T alloc.alloc.Global) :=
  ok { root := false, elems := [] }

@[expose, rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::clear"]
def alloc.collections.btree.set.BTreeSet.clear {T : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (_cloneInst : core.clone.Clone A)
    (_ : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.BTreeSet T A) :=
  ok { root := false, elems := [] }

/-- Inserts the items in order; an item equal to an element already present is dropped (the
    set keeps its element). -/
@[expose, rust_fun
  "alloc::collections::btree::set::{core::iter::traits::collect::Extend<alloc::collections::btree::set::BTreeSet<@T, @A>, @T>}::extend"]
def alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectExtend.extend {T : Type _}
    {A : Type _} {Iter : Type _} {Clause2_IntoIter : Type _} (ordT : core.cmp.Ord T)
    (_allocInst : core.alloc.AllocatorClone A)
    (intoIterInst : core.iter.traits.collect.IntoIterator Iter T Clause2_IntoIter)
    (s : alloc.collections.btree.set.BTreeSet T A) (iter : Iter) :
    Result (alloc.collections.btree.set.BTreeSet T A) := do
  let it ← intoIterInst.into_iter iter
  let items ← AllocModel.iterToList intoIterInst.iteratorInst it []
  items.foldlM (fun (s : alloc.collections.btree.set.BTreeSet T A) (x : T) => do
      let (i, found) ← BTreeMapModel.search (V := Unit) ordT.cmp x (s.elems.map fun y => (y, ()))
      if found then ok s
      else ok { root := true, elems := s.elems.insertIdx i x }) s

/-- `BTreeSet::difference`'s choice of strategy. -/
@[expose] def BTreeSetModel.differenceInner {T : Type u} (ordT : core.cmp.Ord T)
    (s o : List T) : Result (DifferenceInner T) :=
  match s.head?, s.getLast?, o.head?, o.getLast? with
  | some selfMin, some selfMax, some otherMin, some otherMax => do
    let c1 ← ordT.cmp selfMin otherMax
    let c2 ← ordT.cmp selfMax otherMin
    ok (match c1, c2 with
      | .gt, _ | _, .lt => .iterate s
      | .eq, _ => .iterate s.tail
      | _, .eq => .iterate s.dropLast
      | _, _ =>
        if s.length ≤ o.length / 16 then .search s o
        else .stitch s o)
  | _, _, _, _ => ok (.iterate s)

@[expose, rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::difference"]
def alloc.collections.btree.set.BTreeSet.difference {T : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (ordT : core.cmp.Ord T)
    (s other : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.Difference T A) := do
  let inner ← differenceInner ordT s.elems other.elems
  ok { inner }

@[expose, rust_fun
  "alloc::collections::btree::set::{core::iter::traits::iterator::Iterator<alloc::collections::btree::set::Difference<'a, @T, @A>, &'a @T>}::size_hint"]
def alloc.collections.btree.set.Difference.Insts.CoreIterTraitsIteratorIteratorSharedAT.size_hint
    {T : Type _} {A : Type _} (_ordT : core.cmp.Ord T) (_allocInst : core.alloc.AllocatorClone A)
    (d : alloc.collections.btree.set.Difference T A) : Result (Usize × (Option Usize)) := do
  let lens : Nat × Nat :=
    match d.inner with
    | .stitch s o => (s.length, o.length)
    | .search s o => (s.length, o.length)
    | .iterate s => (s.length, 0)
  let lo ← AllocModel.usize (lens.1 - lens.2)
  let hi ← AllocModel.usize lens.1
  ok (lo, some hi)

@[expose] def BTreeSetModel.stitchNext {T : Type u} (ordT : core.cmp.Ord T) (selfNext : T)
    (selfRest otherRest : List T) : Result (Option T × List T × List T) :=
  match otherRest with
  | [] => ok (some selfNext, selfRest, otherRest)
  | o :: os => do
    let c ← ordT.cmp selfNext o
    match c with
    | .lt => ok (some selfNext, selfRest, otherRest)
    | .eq =>
      match selfRest with
      | [] => ok (none, [], otherRest)
      | x :: xs => stitchNext ordT x xs os
    | .gt => stitchNext ordT selfNext selfRest os
termination_by (selfRest.length + otherRest.length)

@[expose] def BTreeSetModel.searchNext {T : Type u} (ordT : core.cmp.Ord T) (other : List T) :
    List T → Result (Option T × List T)
  | [] => ok (none, [])
  | x :: xs => do
    let b ← contains ordT x other
    if b then searchNext ordT other xs else ok (some x, xs)

@[expose, rust_fun
  "alloc::collections::btree::set::{core::iter::traits::iterator::Iterator<alloc::collections::btree::set::Difference<'a, @T, @A>, &'a @T>}::next"]
def alloc.collections.btree.set.Difference.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    {T : Type _} {A : Type _} (ordT : core.cmp.Ord T) (_allocInst : core.alloc.AllocatorClone A)
    (d : alloc.collections.btree.set.Difference T A) :
    Result ((Option T) × (alloc.collections.btree.set.Difference T A)) :=
  match d.inner with
  | .stitch [] o => ok (none, { inner := .stitch [] o })
  | .stitch (x :: xs) o => do
    let (r, s, o) ← stitchNext ordT x xs o
    ok (r, { inner := .stitch s o })
  | .search s o => do
    let (r, s) ← searchNext ordT o s
    ok (r, { inner := .search s o })
  | .iterate [] => ok (none, d)
  | .iterate (x :: xs) => ok (some x, { inner := .iterate xs })

end Aeneas.Std
