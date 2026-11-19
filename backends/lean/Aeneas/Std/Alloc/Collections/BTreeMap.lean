/- `alloc::collections::btree::map`: `BTreeMap` as the list of its entries sorted by key.

Iteration order (ascending keys), lookup results and the kept key on re-insertion (the old
one) are those of Rust. The B-tree search compares keys in a different sequence than this linear
search; comparisons (`Ord::cmp`) are assumed to be pure, so this is unobservable.
`root` records whether Rust's map has allocated its root node (`root.is_some()`): it is observable
through the panics of `range`, which are only raised on a map with a root. -/
module
public import Aeneas.Std.Alloc.Util
public import Aeneas.Std.Alloc.AllocatorClone
public import Aeneas.Std.Core.Borrow
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Default
public import Aeneas.Std.Core.RangeBounds
public section

namespace Aeneas.Std

open Result

@[rust_type "alloc::collections::btree::map::BTreeMap" (body := .opaque)]
structure alloc.collections.btree.map.BTreeMap (K : Type u) (V : Type v) (A : Type w) where
  root : Bool
  entries : List (K × V)

/-- A handle on the entry at `index`, holding its key and (current) value. -/
@[rust_type "alloc::collections::btree::map::entry::OccupiedEntry" (mutRegions := #[0])
  (body := .opaque)]
structure alloc.collections.btree.map.entry.OccupiedEntry (K : Type u) (V : Type v) (A : Type w)
  where
  index : Nat
  key : K
  value : V

/-- A handle on the insertion position `index` of `key`; `value` is the inserted value, if any. -/
@[rust_type "alloc::collections::btree::map::entry::VacantEntry" (mutRegions := #[0])
  (body := .opaque)]
structure alloc.collections.btree.map.entry.VacantEntry (K : Type u) (V : Type v) (A : Type w)
  where
  index : Nat
  key : K
  value : Option V

@[rust_type "alloc::collections::btree::map::entry::Entry" (mutRegions := #[0])]
inductive alloc.collections.btree.map.entry.Entry (K : Type u) (V : Type v) (A : Type w) where
| Vacant : alloc.collections.btree.map.entry.VacantEntry K V A →
  alloc.collections.btree.map.entry.Entry K V A
| Occupied : alloc.collections.btree.map.entry.OccupiedEntry K V A →
  alloc.collections.btree.map.entry.Entry K V A

@[rust_type "alloc::collections::btree::map::Iter" (body := .opaque)]
structure alloc.collections.btree.map.Iter (K : Type u) (V : Type v) where
  rest : List (K × V)

@[rust_type "alloc::collections::btree::map::Range" (body := .opaque)]
structure alloc.collections.btree.map.Range (K : Type u) (V : Type v) where
  rest : List (K × V)

/-- The entries of the map and the position of the next value to yield. -/
@[rust_type "alloc::collections::btree::map::ValuesMut" (mutRegions := #[0]) (body := .opaque)]
structure alloc.collections.btree.map.ValuesMut (K : Type u) (V : Type v) where
  entries : List (K × V)
  pos : Nat

namespace BTreeMapModel

/-- Search `key` (compared with `cmp key k`, as Rust's `search_tree`).
    Returns `(index, found)`: the position of the equal key, or the insertion position. -/
@[expose] def search {K : Type u} {V : Type v} {Q : Type w} (cmp : Q → K → Result Ordering)
    (key : Q) : List (K × V) → Result (Nat × Bool)
  | [] => ok (0, false)
  | (k, _) :: rest => do
    let c ← cmp key k
    match c with
    | .gt => do
      let (i, found) ← search cmp key rest
      ok (i + 1, found)
    | .eq => ok (0, true)
    | .lt => ok (0, false)

/-- Compare a borrowed key with a key of the map. -/
@[expose] def cmpBorrowed {K : Type u} {Q : Type v} (borrowInst : core.borrow.Borrow K Q)
    (ordQ : core.cmp.Ord Q) (q : Q) (k : K) : Result Ordering := do
  let kq ← borrowInst.borrow k
  ordQ.cmp q kq

/-- Rust's `range_search` checks: panics when the start bound is greater than the end bound,
    or both are equal and excluded. -/
@[expose] def checkRange {T : Type u} (ordT : core.cmp.Ord T)
    (sb eb : core.ops.range.Bound T) : Result Unit := do
  let gtCheck := fun (s e : T) => do
    let gt ← ordT.partialOrdInst.gt s e
    if gt then fail .panic else ok ()
  match sb, eb with
  | .Excluded s, .Excluded e => do
    let eq ← ordT.eqInst.partialEqInst.eq s e
    if eq then fail .panic else gtCheck s e
  | .Included s, .Included e => gtCheck s e
  | .Included s, .Excluded e => gtCheck s e
  | .Excluded s, .Included e => gtCheck s e
  | _, _ => ok ()

/-- Whether the borrowed key `kq` lies within the bounds (comparisons `bound.cmp(key)`). -/
@[expose] def inRange {T : Type u} (ordT : core.cmp.Ord T) (sb eb : core.ops.range.Bound T)
    (kq : T) : Result Bool := do
  let above ← match sb with
    | .Included s => do
      let c ← ordT.cmp s kq
      ok (c != .gt)
    | .Excluded s => do
      let c ← ordT.cmp s kq
      ok (c == .lt)
    | .Unbounded => ok true
  if above then
    match eb with
    | .Included e => do
      let c ← ordT.cmp e kq
      ok (c != .lt)
    | .Excluded e => do
      let c ← ordT.cmp e kq
      ok (c == .gt)
    | .Unbounded => ok true
  else ok false

end BTreeMapModel

open BTreeMapModel

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, alloc::alloc::Global>}::new"]
def alloc.collections.btree.map.BTreeMapKVGlobal.new (K : Type _) (V : Type _) :
    Result (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global) :=
  ok { root := false, entries := [] }

@[expose, rust_fun
  "alloc::collections::btree::map::{core::default::Default<alloc::collections::btree::map::BTreeMap<@K, @V, alloc::alloc::Global>>}::default"]
def alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default
    (K : Type _) (V : Type _) :
    Result (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global) :=
  ok { root := false, entries := [] }

/-- Clones the keys and values in ascending order (key, then value), as `clone_subtree`. An empty
    map is cloned as a fresh map (no root). -/
@[expose, rust_fun
  "alloc::collections::btree::map::{core::clone::Clone<alloc::collections::btree::map::BTreeMap<@K, @V, @A>>}::clone"]
def alloc.collections.btree.map.BTreeMap.Insts.CoreCloneClone.clone {K : Type _} {V : Type _}
    {A : Type _} (cloneK : core.clone.Clone K) (cloneV : core.clone.Clone V)
    (_allocInst : core.alloc.AllocatorClone A) (m : alloc.collections.btree.map.BTreeMap K V A) :
    Result (alloc.collections.btree.map.BTreeMap K V A) := do
  if m.entries.isEmpty then ok { root := false, entries := [] }
  else
    let entries ← m.entries.mapM fun (k, v) => do
      let k ← cloneK.clone k
      let v ← cloneV.clone v
      ok (k, v)
    ok { root := true, entries }

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::clear"]
def alloc.collections.btree.map.BTreeMap.clear {K : Type _} {V : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (_ : alloc.collections.btree.map.BTreeMap K V A) :
    Result (alloc.collections.btree.map.BTreeMap K V A) :=
  ok { root := false, entries := [] }

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::get"]
def alloc.collections.btree.map.BTreeMap.get {K : Type _} {V : Type _} {A : Type _} {Q : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (borrowInst : core.borrow.Borrow K Q)
    (_ordK : core.cmp.Ord K) (ordQ : core.cmp.Ord Q)
    (m : alloc.collections.btree.map.BTreeMap K V A) (key : Q) : Result (Option V) := do
  let (i, found) ← search (cmpBorrowed borrowInst ordQ) key m.entries
  ok (if found then (m.entries[i]?.map Prod.snd) else none)

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::contains_key"]
def alloc.collections.btree.map.BTreeMap.contains_key {K : Type _} {V : Type _} {A : Type _}
    {Q : Type _} (_allocInst : core.alloc.AllocatorClone A) (borrowInst : core.borrow.Borrow K Q)
    (_ordK : core.cmp.Ord K) (ordQ : core.cmp.Ord Q)
    (m : alloc.collections.btree.map.BTreeMap K V A) (key : Q) : Result Bool := do
  let (_, found) ← search (cmpBorrowed borrowInst ordQ) key m.entries
  ok found

/-- On an existing key, replaces the value and keeps the old key. -/
@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::insert"]
def alloc.collections.btree.map.BTreeMap.insert {K : Type _} {V : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (ordK : core.cmp.Ord K)
    (m : alloc.collections.btree.map.BTreeMap K V A) (key : K) (value : V) :
    Result ((Option V) × (alloc.collections.btree.map.BTreeMap K V A)) := do
  let (i, found) ← search ordK.cmp key m.entries
  if found then
    match m.entries[i]? with
    | some (k, old) => ok (some old, { m with entries := m.entries.set i (k, value) })
    | none => fail .panic
  else ok (none, { root := true, entries := m.entries.insertIdx i (key, value) })

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::remove"]
def alloc.collections.btree.map.BTreeMap.remove {K : Type _} {V : Type _} {A : Type _}
    {Q : Type _} (_allocInst : core.alloc.AllocatorClone A) (borrowInst : core.borrow.Borrow K Q)
    (_ordK : core.cmp.Ord K) (ordQ : core.cmp.Ord Q)
    (m : alloc.collections.btree.map.BTreeMap K V A) (key : Q) :
    Result ((Option V) × (alloc.collections.btree.map.BTreeMap K V A)) := do
  let (i, found) ← search (cmpBorrowed borrowInst ordQ) key m.entries
  if found then
    match m.entries[i]? with
    | some (_, v) => ok (some v, { m with entries := m.entries.eraseIdx i })
    | none => fail .panic
  else ok (none, m)

/-- Calls the predicate once on every entry, in ascending key order, and keeps the entries for
    which it returns `true`. The predicate receives `&mut V`, but the extracted closure signature
    (`FnMut F (K × V) Bool`) cannot return an updated value: values are kept unchanged. -/
@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::retain"]
def alloc.collections.btree.map.BTreeMap.retain {K : Type _} {V : Type _} {A : Type _} {F : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (_ordK : core.cmp.Ord K)
    (fnInst : core.ops.function.FnMut F (K × V) Bool)
    (m : alloc.collections.btree.map.BTreeMap K V A) (f : F) :
    Result (alloc.collections.btree.map.BTreeMap K V A) := do
  let entries ← AllocModel.retainList fnInst.call_mut f [] m.entries
  ok { m with entries }

/-- Panics (on a map with a root, as Rust) when the start bound is greater than the end bound,
    or both are equal and excluded. -/
@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::range"]
def alloc.collections.btree.map.BTreeMap.range {K : Type _} {V : Type _} {A : Type _} {T : Type _}
    {R : Type _} (_allocInst : core.alloc.AllocatorClone A) (ordT : core.cmp.Ord T)
    (borrowInst : core.borrow.Borrow K T) (_ordK : core.cmp.Ord K)
    (rangeInst : core.ops.range.RangeBounds R T)
    (m : alloc.collections.btree.map.BTreeMap K V A) (r : R) :
    Result (alloc.collections.btree.map.Range K V) := do
  if m.root then do
    let sb ← rangeInst.start_bound r
    let eb ← rangeInst.end_bound r
    let _ ← checkRange ordT sb eb
    let rest ← m.entries.filterM fun (kv : K × V) => do
      let kq ← borrowInst.borrow kv.1
      inRange ordT sb eb kq
    ok { rest }
  else ok { rest := [] }

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::entry"]
def alloc.collections.btree.map.BTreeMap.entry {K : Type _} {V : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (ordK : core.cmp.Ord K)
    (m : alloc.collections.btree.map.BTreeMap K V A) (key : K) :
    Result ((alloc.collections.btree.map.entry.Entry K V A) ×
      (alloc.collections.btree.map.entry.Entry K V A → alloc.collections.btree.map.BTreeMap K V A)) := do
  let (i, found) ← search ordK.cmp key m.entries
  let back := fun (e : alloc.collections.btree.map.entry.Entry K V A) =>
    (match e with
    | .Occupied o =>
      match m.entries[o.index]? with
      | some (k, _) => { m with entries := m.entries.set o.index (k, o.value) }
      | none => m
    | .Vacant ve =>
      match ve.value with
      | some v => { root := true, entries := m.entries.insertIdx ve.index (ve.key, v) }
      | none => m : alloc.collections.btree.map.BTreeMap K V A)
  if found then
    match m.entries[i]? with
    | some (k, v) => ok (.Occupied { index := i, key := k, value := v }, back)
    | none => fail .panic
  else ok (.Vacant { index := i, key := key, value := none }, back)

/-- `Entry::or_default`. Output: (the value, backward function giving the final entry). -/
@[expose, rust_fun
  "alloc::collections::btree::map::entry::{alloc::collections::btree::map::entry::Entry<'a, @K, @V, @A>}::or_default"]
def alloc.collections.btree.map.entry.Entry.or_default {K : Type _} {V : Type _} {A : Type _}
    (_ordK : core.cmp.Ord K) (defaultInst : core.default.Default V)
    (_allocInst : core.alloc.AllocatorClone A) (e : alloc.collections.btree.map.entry.Entry K V A) :
    Result (V × (V → alloc.collections.btree.map.entry.Entry K V A)) := do
  match e with
  | .Occupied o => ok (o.value, fun v => .Occupied { o with value := v })
  | .Vacant ve =>
    let v ← defaultInst.default
    ok (v, fun v => .Vacant { ve with value := some v })

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::iter"]
def alloc.collections.btree.map.BTreeMap.iter {K : Type _} {V : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (m : alloc.collections.btree.map.BTreeMap K V A) :
    Result (alloc.collections.btree.map.Iter K V) :=
  ok { rest := m.entries }

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::values_mut"]
def alloc.collections.btree.map.BTreeMap.values_mut {K : Type _} {V : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (m : alloc.collections.btree.map.BTreeMap K V A) :
    Result ((alloc.collections.btree.map.ValuesMut K V) ×
      (alloc.collections.btree.map.ValuesMut K V → alloc.collections.btree.map.BTreeMap K V A)) :=
  ok ({ entries := m.entries, pos := 0 }, fun it => { m with entries := it.entries })

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::len"]
def alloc.collections.btree.map.BTreeMap.len {K : Type _} {V : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (m : alloc.collections.btree.map.BTreeMap K V A) :
    Result Usize :=
  AllocModel.usize m.entries.length

@[expose, rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::is_empty"]
def alloc.collections.btree.map.BTreeMap.is_empty {K : Type _} {V : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (m : alloc.collections.btree.map.BTreeMap K V A) :
    Result Bool :=
  ok m.entries.isEmpty

/-! ## Iterators -/

@[expose, rust_fun
  "alloc::collections::btree::map::{core::iter::traits::iterator::Iterator<alloc::collections::btree::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::next"]
def alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next
    {K : Type _} {V : Type _} (it : alloc.collections.btree.map.Iter K V) :
    Result ((Option (K × V)) × (alloc.collections.btree.map.Iter K V)) :=
  match it.rest with
  | [] => ok (none, it)
  | kv :: rest => ok (some kv, { rest })

/-- `Range::max` is `next_back`. -/
@[expose, rust_fun
  "alloc::collections::btree::map::{core::iter::traits::iterator::Iterator<alloc::collections::btree::map::Range<'a, @K, @V>, (&'a @K, &'a @V)>}::max"]
def alloc.collections.btree.map.Range.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.max
    {K : Type _} {V : Type _} (_ordInst : core.cmp.Ord (K × V))
    (it : alloc.collections.btree.map.Range K V) : Result (Option (K × V)) :=
  ok it.rest.getLast?

/-- `Range::last` is `next_back`. -/
@[expose, rust_fun
  "alloc::collections::btree::map::{core::iter::traits::iterator::Iterator<alloc::collections::btree::map::Range<'a, @K, @V>, (&'a @K, &'a @V)>}::last"]
def alloc.collections.btree.map.Range.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.last
    {K : Type _} {V : Type _} (it : alloc.collections.btree.map.Range K V) :
    Result (Option (K × V)) :=
  ok it.rest.getLast?

@[expose, rust_fun
  "alloc::collections::btree::map::{core::iter::traits::iterator::Iterator<alloc::collections::btree::map::Range<'a, @K, @V>, (&'a @K, &'a @V)>}::next"]
def alloc.collections.btree.map.Range.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next
    {K : Type _} {V : Type _} (it : alloc.collections.btree.map.Range K V) :
    Result ((Option (K × V)) × (alloc.collections.btree.map.Range K V)) :=
  match it.rest with
  | [] => ok (none, it)
  | kv :: rest => ok (some kv, { rest })

/-- Output: (the value, the advanced iterator, backward function writing the final value back
    into the iterator state). -/
@[expose, rust_fun
  "alloc::collections::btree::map::{core::iter::traits::iterator::Iterator<alloc::collections::btree::map::ValuesMut<'a, @K, @V>, &'a mut @V>}::next"]
def alloc.collections.btree.map.ValuesMut.Insts.CoreIterTraitsIteratorIteratorMutAV.next
    {K : Type _} {V : Type _} (it : alloc.collections.btree.map.ValuesMut K V) :
    Result ((Option V) × (alloc.collections.btree.map.ValuesMut K V) ×
      (alloc.collections.btree.map.ValuesMut K V → Option V →
        alloc.collections.btree.map.ValuesMut K V)) :=
  match it.entries[it.pos]? with
  | none => ok (none, it, fun it _ => it)
  | some (_, v) =>
    let i := it.pos
    let back (it' : alloc.collections.btree.map.ValuesMut K V) (o : Option V) :
        alloc.collections.btree.map.ValuesMut K V :=
      match o, it'.entries[i]? with
      | some v', some (k, _) => { it' with entries := it'.entries.set i (k, v') }
      | _, _ => it'
    ok (some v, { it with pos := i + 1 }, back)

end Aeneas.Std
