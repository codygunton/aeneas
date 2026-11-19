/- `std::collections::hash::{map, set}`: `HashMap` and `HashSet` as insertion-ordered
association lists with unique keys.

Iteration order: Rust's order depends on the hash of the keys and on the table history. With
`RandomState` (the default) it is randomized per map, so any deterministic order is a faithful
choice: the model iterates in insertion order (removal keeps the relative order of the remaining
entries). With a deterministic hasher (e.g. `rustc_hash::FxBuildHasher`) Rust's order is
deterministic and this model does NOT reproduce it; the extracted code never iterates such a map
(see `extract/reports/hash-iteration-sites.json`).

Lookups compare keys with `Eq` (through `Borrow`), as hashbrown does on hash-tag matches; keys
are not hashed, which is unobservable for pure `Hash` implementations. On an existing key,
`insert` replaces the value and keeps the old key (`HashSet::insert` keeps the old element). -/
module
public import Aeneas.Std.Alloc.Util
public import Aeneas.Std.Core.Borrow
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Default
public import Aeneas.Std.Core.Hash
public import Aeneas.Std.Std.Hash
public section

namespace Aeneas.Std

open Result

@[rust_type "std::collections::hash::map::HashMap" (body := .opaque)]
structure std.collections.hash.map.HashMap (K : Type u) (V : Type v) (S : Type w) (A : Type x)
  where
  hash_builder : S
  entries : List (K × V)

@[rust_type "std::collections::hash::map::Iter" (body := .opaque)]
structure std.collections.hash.map.Iter (K : Type u) (V : Type v) where
  rest : List (K × V)

@[rust_type "std::collections::hash::map::Values" (body := .opaque)]
structure std.collections.hash.map.Values (K : Type u) (V : Type v) where
  rest : List V

/-- A handle on the entry at `index` of the map, holding its (current) value. -/
@[rust_type "std::collections::hash::map::OccupiedEntry" (mutRegions := #[0]) (body := .opaque)]
structure std.collections.hash.map.OccupiedEntry (K : Type u) (V : Type v) (A : Type w) where
  index : Nat
  key : K
  value : V

/-- A handle on a missing `key`; `value` is the inserted value, if any. -/
@[rust_type "std::collections::hash::map::VacantEntry" (mutRegions := #[0]) (body := .opaque)]
structure std.collections.hash.map.VacantEntry (K : Type u) (V : Type v) (A : Type w) where
  key : K
  value : Option V

@[rust_type "std::collections::hash::map::Entry" (mutRegions := #[0])]
inductive std.collections.hash.map.Entry (K : Type u) (V : Type v) (A : Type w) where
| Occupied : std.collections.hash.map.OccupiedEntry K V A → std.collections.hash.map.Entry K V A
| Vacant : std.collections.hash.map.VacantEntry K V A → std.collections.hash.map.Entry K V A

@[rust_type "std::collections::hash::set::HashSet" (body := .opaque)]
structure std.collections.hash.set.HashSet (T : Type u) (S : Type v) (A : Type w) where
  hash_builder : S
  elems : List T

@[rust_type "std::collections::hash::set::Iter" (body := .opaque)]
structure std.collections.hash.set.Iter (K : Type u) where
  rest : List K

@[rust_type "std::collections::hash::set::IntoIter" (body := .opaque)]
structure std.collections.hash.set.IntoIter (K : Type u) (A : Type v) where
  rest : List K

namespace HashModel

/-- Index of the first element `x` with `eq q (key x)`. -/
@[expose] def findIdx {X : Type u} {Q : Type v} (eq : Q → Q → Result Bool) (key : X → Result Q)
    (q : Q) : List X → Result (Option Nat)
  | [] => ok none
  | x :: xs => do
    let k ← key x
    let b ← eq q k
    if b then ok (some 0)
    else do
      let r ← findIdx eq key q xs
      ok (r.map (· + 1))

/-- Find a borrowed key `q` among the entries: `q == k.borrow()`. -/
@[expose] def findBorrowed {K : Type u} {V : Type v} {Q : Type w}
    (borrowInst : core.borrow.Borrow K Q) (eqQ : core.cmp.Eq Q) (q : Q) (l : List (K × V)) :
    Result (Option Nat) :=
  findIdx eqQ.partialEqInst.eq (fun (kv : K × V) => borrowInst.borrow kv.1) q l

/-- Find a key `k` among the entries: `k == k'`. -/
@[expose] def findKey {K : Type u} {V : Type v} (eqK : core.cmp.Eq K) (k : K) (l : List (K × V)) :
    Result (Option Nat) :=
  findIdx eqK.partialEqInst.eq (fun (kv : K × V) => ok kv.1) k l

end HashModel

open HashModel

/-! ## `HashMap` -/

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, std::hash::random::RandomState, alloc::alloc::Global>}::new"]
def std.collections.hash.map.HashMapKVRandomStateGlobal.new (K : Type _) (V : Type _) :
    Result (std.collections.hash.map.HashMap K V std.hash.random.RandomState alloc.alloc.Global) := do
  let s ← std.hash.random.RandomState.Insts.CoreDefaultDefault.default
  ok { hash_builder := s, entries := [] }

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, std::hash::random::RandomState, alloc::alloc::Global>}::with_capacity"]
def std.collections.hash.map.HashMapKVRandomStateGlobal.with_capacity (K : Type _) (V : Type _)
    (_ : Usize) :
    Result (std.collections.hash.map.HashMap K V std.hash.random.RandomState alloc.alloc.Global) :=
  std.collections.hash.map.HashMapKVRandomStateGlobal.new K V

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, alloc::alloc::Global>}::with_capacity_and_hasher"]
def std.collections.hash.map.HashMapKVSGlobal.with_capacity_and_hasher (K : Type _) (V : Type _)
    {S : Type _} (_ : Usize) (s : S) :
    Result (std.collections.hash.map.HashMap K V S alloc.alloc.Global) :=
  ok { hash_builder := s, entries := [] }

@[expose, rust_fun
  "std::collections::hash::map::{core::default::Default<std::collections::hash::map::HashMap<@K, @V, @S, alloc::alloc::Global>>}::default"]
def std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault.default (K : Type _)
    (V : Type _) {S : Type _} (defaultInst : core.default.Default S) :
    Result (std.collections.hash.map.HashMap K V S alloc.alloc.Global) := do
  let s ← defaultInst.default
  ok { hash_builder := s, entries := [] }

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::values"]
def std.collections.hash.map.HashMap.values {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    (m : std.collections.hash.map.HashMap K V S A) : Result (std.collections.hash.map.Values K V) :=
  ok { rest := m.entries.map Prod.snd }

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::iter"]
def std.collections.hash.map.HashMap.iter {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    (m : std.collections.hash.map.HashMap K V S A) : Result (std.collections.hash.map.Iter K V) :=
  ok { rest := m.entries }

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::len"]
def std.collections.hash.map.HashMap.len {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    (m : std.collections.hash.map.HashMap K V S A) : Result Usize :=
  AllocModel.usize m.entries.length

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::is_empty"]
def std.collections.hash.map.HashMap.is_empty {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    (m : std.collections.hash.map.HashMap K V S A) : Result Bool :=
  ok m.entries.isEmpty

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::entry"]
def std.collections.hash.map.HashMap.entry {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    {Clause2_Hasher : Type _} (eqK : core.cmp.Eq K) (_hashK : core.hash.Hash K)
    (_buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (m : std.collections.hash.map.HashMap K V S A) (key : K) :
    Result ((std.collections.hash.map.Entry K V A) ×
      (std.collections.hash.map.Entry K V A → std.collections.hash.map.HashMap K V S A)) := do
  let back := fun (e : std.collections.hash.map.Entry K V A) =>
    (match e with
    | .Occupied o =>
      match m.entries[o.index]? with
      | some (k, _) => { m with entries := m.entries.set o.index (k, o.value) }
      | none => m
    | .Vacant ve =>
      match ve.value with
      | some v => { m with entries := m.entries ++ [(ve.key, v)] }
      | none => m : std.collections.hash.map.HashMap K V S A)
  let idx ← findKey eqK key m.entries
  match idx with
  | some i =>
    match m.entries[i]? with
    | some (k, v) => ok (.Occupied { index := i, key := k, value := v }, back)
    | none => fail .panic
  | none => ok (.Vacant { key, value := none }, back)

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get"]
def std.collections.hash.map.HashMap.get {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    {Q : Type _} {Clause2_Hasher : Type _} (_eqK : core.cmp.Eq K) (_hashK : core.hash.Hash K)
    (_buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (borrowInst : core.borrow.Borrow K Q) (_hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (m : std.collections.hash.map.HashMap K V S A) (key : Q) : Result (Option V) := do
  let idx ← findBorrowed borrowInst eqQ key m.entries
  match idx with
  | some i => ok (m.entries[i]?.map Prod.snd)
  | none => ok none

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::contains_key"]
def std.collections.hash.map.HashMap.contains_key {K : Type _} {V : Type _} {S : Type _}
    {A : Type _} {Q : Type _} {Clause2_Hasher : Type _} (_eqK : core.cmp.Eq K)
    (_hashK : core.hash.Hash K) (_buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (borrowInst : core.borrow.Borrow K Q) (_hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (m : std.collections.hash.map.HashMap K V S A) (key : Q) : Result Bool := do
  let idx ← findBorrowed borrowInst eqQ key m.entries
  ok idx.isSome

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::insert"]
def std.collections.hash.map.HashMap.insert {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    {Clause2_Hasher : Type _} (eqK : core.cmp.Eq K) (_hashK : core.hash.Hash K)
    (_buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (m : std.collections.hash.map.HashMap K V S A) (key : K) (value : V) :
    Result ((Option V) × (std.collections.hash.map.HashMap K V S A)) := do
  let idx ← findKey eqK key m.entries
  match idx with
  | some i =>
    match m.entries[i]? with
    | some (k, old) => ok (some old, { m with entries := m.entries.set i (k, value) })
    | none => fail .panic
  | none => ok (none, { m with entries := m.entries ++ [(key, value)] })

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::remove"]
def std.collections.hash.map.HashMap.remove {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    {Q : Type _} {Clause2_Hasher : Type _} (_eqK : core.cmp.Eq K) (_hashK : core.hash.Hash K)
    (_buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (borrowInst : core.borrow.Borrow K Q) (_hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (m : std.collections.hash.map.HashMap K V S A) (key : Q) :
    Result ((Option V) × (std.collections.hash.map.HashMap K V S A)) := do
  let idx ← findBorrowed borrowInst eqQ key m.entries
  match idx with
  | some i =>
    match m.entries[i]? with
    | some (_, v) => ok (some v, { m with entries := m.entries.eraseIdx i })
    | none => fail .panic
  | none => ok (none, m)

/-- `map[key]`: panics if the key is absent. -/
@[expose, rust_fun
  "std::collections::hash::map::{core::ops::index::Index<std::collections::hash::map::HashMap<@K, @V, @S, @A>, &'0 @Q, @V>}::index"]
def std.collections.hash.map.HashMap.Insts.CoreOpsIndexIndexShared0QV.index {K : Type _}
    {Q : Type _} {V : Type _} {S : Type _} {A : Type _} {Clause5_Hasher : Type _}
    (_eqK : core.cmp.Eq K) (_hashK : core.hash.Hash K) (borrowInst : core.borrow.Borrow K Q)
    (eqQ : core.cmp.Eq Q) (_hashQ : core.hash.Hash Q)
    (_buildHasherInst : core.hash.BuildHasher S Clause5_Hasher)
    (m : std.collections.hash.map.HashMap K V S A) (key : Q) : Result V := do
  let idx ← findBorrowed borrowInst eqQ key m.entries
  match idx with
  | some i =>
    match m.entries[i]? with
    | some (_, v) => ok v
    | none => fail .panic
  | none => fail .panic

@[expose, rust_fun
  "std::collections::hash::map::{core::iter::traits::collect::IntoIterator<&'a std::collections::hash::map::HashMap<@K, @V, @S, @A>, (&'a @K, &'a @V), std::collections::hash::map::Iter<'a, @K, @V>>}::into_iter"]
def SharedAHashMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    {K : Type _} {V : Type _} {S : Type _} {A : Type _}
    (m : std.collections.hash.map.HashMap K V S A) : Result (std.collections.hash.map.Iter K V) :=
  ok { rest := m.entries }

/-- `HashMap::from_iter`: `with_hasher(S::default())`, then `insert` every pair in order. -/
@[expose, rust_fun
  "std::collections::hash::map::{core::iter::traits::collect::FromIterator<std::collections::hash::map::HashMap<@K, @V, @S, alloc::alloc::Global>, (@K, @V)>}::from_iter"]
def std.collections.hash.map.HashMapKVSGlobal.Insts.CoreIterTraitsCollectFromIteratorPair.from_iter
    {K : Type _} {V : Type _} {S : Type _} {I : Type _} {Clause2_Hasher : Type _}
    {Clause4_IntoIter : Type _} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (defaultInst : core.default.Default S)
    (intoIterInst : core.iter.traits.collect.IntoIterator I (K × V) Clause4_IntoIter) (iter : I) :
    Result (std.collections.hash.map.HashMap K V S alloc.alloc.Global) := do
  let s ← defaultInst.default
  let it ← intoIterInst.into_iter iter
  let items ← AllocModel.iterToList intoIterInst.iteratorInst it []
  items.foldlM (fun m (k, v) => do
      let (_, m) ← std.collections.hash.map.HashMap.insert eqK hashK buildHasherInst m k v
      ok m)
    ({ hash_builder := s, entries := [] } :
      std.collections.hash.map.HashMap K V S alloc.alloc.Global)

/-! ## `HashMap` iterators -/

@[expose, rust_fun
  "std::collections::hash::map::{core::iter::traits::iterator::Iterator<std::collections::hash::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::fold"]
def std.collections.hash.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.fold
    {K : Type _} {V : Type _} {B : Type _} {F : Type _}
    (fnInst : core.ops.function.FnMut F (B × (K × V)) B)
    (it : std.collections.hash.map.Iter K V) (init : B) (f : F) : Result B :=
  AllocModel.foldList fnInst.call_mut f init it.rest

@[expose, rust_fun
  "std::collections::hash::map::{core::iter::traits::iterator::Iterator<std::collections::hash::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::count"]
def std.collections.hash.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.count
    {K : Type _} {V : Type _} (it : std.collections.hash.map.Iter K V) : Result Usize :=
  AllocModel.usize it.rest.length

@[expose, rust_fun
  "std::collections::hash::map::{core::iter::traits::iterator::Iterator<std::collections::hash::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::size_hint"]
def std.collections.hash.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.size_hint
    {K : Type _} {V : Type _} (it : std.collections.hash.map.Iter K V) :
    Result (Usize × (Option Usize)) :=
  AllocModel.exactSizeHint it.rest.length

@[expose, rust_fun
  "std::collections::hash::map::{core::iter::traits::iterator::Iterator<std::collections::hash::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::next"]
def std.collections.hash.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next
    {K : Type _} {V : Type _} (it : std.collections.hash.map.Iter K V) :
    Result ((Option (K × V)) × (std.collections.hash.map.Iter K V)) :=
  match it.rest with
  | [] => ok (none, it)
  | kv :: rest => ok (some kv, { rest })

@[expose, rust_fun
  "std::collections::hash::map::{core::iter::traits::iterator::Iterator<std::collections::hash::map::Values<'a, @K, @V>, &'a @V>}::next"]
def std.collections.hash.map.Values.Insts.CoreIterTraitsIteratorIteratorSharedAV.next
    {K : Type _} {V : Type _} (it : std.collections.hash.map.Values K V) :
    Result ((Option V) × (std.collections.hash.map.Values K V)) :=
  match it.rest with
  | [] => ok (none, it)
  | v :: rest => ok (some v, { rest })

/-! ## Entries -/

/-- Output: (the value, backward function giving the final entry). -/
@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::Entry<'a, @K, @V, @A>}::or_insert_with"]
def std.collections.hash.map.Entry.or_insert_with {K : Type _} {V : Type _} {A : Type _}
    {F : Type _} (fnInst : core.ops.function.FnOnce F Unit V)
    (e : std.collections.hash.map.Entry K V A) (f : F) :
    Result (V × (V → std.collections.hash.map.Entry K V A)) := do
  match e with
  | .Occupied o => ok (o.value, fun v => .Occupied { o with value := v })
  | .Vacant ve =>
    let v ← fnInst.call_once f ()
    ok (v, fun v => .Vacant { ve with value := some v })

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::OccupiedEntry<'a, @K, @V, @A>}::get"]
def std.collections.hash.map.OccupiedEntry.get {K : Type _} {V : Type _} {A : Type _}
    (o : std.collections.hash.map.OccupiedEntry K V A) : Result V :=
  ok o.value

/-- Output: (the inserted value, backward function giving the final entry). -/
@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::VacantEntry<'a, @K, @V, @A>}::insert"]
def std.collections.hash.map.VacantEntry.insert {K : Type _} {V : Type _} {A : Type _}
    (ve : std.collections.hash.map.VacantEntry K V A) (v : V) :
    Result (V × (V → std.collections.hash.map.VacantEntry K V A)) :=
  ok (v, fun v => { ve with value := some v })

/-! ## `HashSet` -/

@[expose, rust_fun
  "std::collections::hash::set::{std::collections::hash::set::HashSet<@T, @S, @A>}::contains"]
def std.collections.hash.set.HashSet.contains {T : Type _} {S : Type _} {A : Type _} {Q : Type _}
    {Clause2_Hasher : Type _} (_eqT : core.cmp.Eq T) (_hashT : core.hash.Hash T)
    (_buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (borrowInst : core.borrow.Borrow T Q) (_hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (s : std.collections.hash.set.HashSet T S A) (x : Q) : Result Bool := do
  let idx ← findIdx eqQ.partialEqInst.eq borrowInst.borrow x s.elems
  ok idx.isSome

/-- Returns `false` (and keeps the old element) when an equal element is present. -/
@[expose, rust_fun
  "std::collections::hash::set::{std::collections::hash::set::HashSet<@T, @S, @A>}::insert"]
def std.collections.hash.set.HashSet.insert {T : Type _} {S : Type _} {A : Type _}
    {Clause2_Hasher : Type _} (eqT : core.cmp.Eq T) (_hashT : core.hash.Hash T)
    (_buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (s : std.collections.hash.set.HashSet T S A) (x : T) :
    Result (Bool × (std.collections.hash.set.HashSet T S A)) := do
  let idx ← findIdx eqT.partialEqInst.eq (fun y => ok y) x s.elems
  match idx with
  | some _ => ok (false, s)
  | none => ok (true, { s with elems := s.elems ++ [x] })

/-- `with_hasher(S::default())`, then `insert` every item in order. -/
@[expose, rust_fun
  "std::collections::hash::set::{core::iter::traits::collect::FromIterator<std::collections::hash::set::HashSet<@T, @S, alloc::alloc::Global>, @T>}::from_iter"]
def std.collections.hash.set.HashSetTSGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter
    {T : Type _} {S : Type _} {I : Type _} {Clause2_Hasher : Type _} {Clause4_IntoIter : Type _}
    (eqT : core.cmp.Eq T) (hashT : core.hash.Hash T)
    (buildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (defaultInst : core.default.Default S)
    (intoIterInst : core.iter.traits.collect.IntoIterator I T Clause4_IntoIter) (iter : I) :
    Result (std.collections.hash.set.HashSet T S alloc.alloc.Global) := do
  let s ← defaultInst.default
  let it ← intoIterInst.into_iter iter
  let items ← AllocModel.iterToList intoIterInst.iteratorInst it []
  items.foldlM (fun set x => do
      let (_, set) ← std.collections.hash.set.HashSet.insert eqT hashT buildHasherInst set x
      ok set)
    ({ hash_builder := s, elems := [] } : std.collections.hash.set.HashSet T S alloc.alloc.Global)

@[expose, rust_fun
  "std::collections::hash::set::{core::default::Default<std::collections::hash::set::HashSet<@T, @S, alloc::alloc::Global>>}::default"]
def std.collections.hash.set.HashSetTSGlobal.Insts.CoreDefaultDefault.default (T : Type _)
    {S : Type _} (defaultInst : core.default.Default S) :
    Result (std.collections.hash.set.HashSet T S alloc.alloc.Global) := do
  let s ← defaultInst.default
  ok { hash_builder := s, elems := [] }

@[expose, rust_fun
  "std::collections::hash::set::{core::iter::traits::collect::IntoIterator<&'a std::collections::hash::set::HashSet<@T, @S, @A>, &'a @T, std::collections::hash::set::Iter<'a, @T>>}::into_iter"]
def SharedAHashSet.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter {T : Type _}
    {S : Type _} {A : Type _} (s : std.collections.hash.set.HashSet T S A) :
    Result (std.collections.hash.set.Iter T) :=
  ok { rest := s.elems }

@[expose, rust_fun
  "std::collections::hash::set::{core::iter::traits::collect::IntoIterator<std::collections::hash::set::HashSet<@T, @S, @A>, @T, std::collections::hash::set::IntoIter<@T, @A>>}::into_iter"]
def std.collections.hash.set.HashSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T : Type _} {S : Type _} {A : Type _} (s : std.collections.hash.set.HashSet T S A) :
    Result (std.collections.hash.set.IntoIter T A) :=
  ok { rest := s.elems }

@[expose, rust_fun
  "std::collections::hash::set::{core::iter::traits::iterator::Iterator<std::collections::hash::set::Iter<'a, @K>, &'a @K>}::next"]
def std.collections.hash.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAK.next {K : Type _}
    (it : std.collections.hash.set.Iter K) :
    Result ((Option K) × (std.collections.hash.set.Iter K)) :=
  match it.rest with
  | [] => ok (none, it)
  | x :: rest => ok (some x, { rest })

@[expose, rust_fun
  "std::collections::hash::set::{core::iter::traits::iterator::Iterator<std::collections::hash::set::IntoIter<@K, @A>, @K>}::next"]
def std.collections.hash.set.IntoIter.Insts.CoreIterTraitsIteratorIterator.next {K : Type _}
    {A : Type _} (it : std.collections.hash.set.IntoIter K A) :
    Result ((Option K) × (std.collections.hash.set.IntoIter K A)) :=
  match it.rest with
  | [] => ok (none, it)
  | x :: rest => ok (some x, { rest })

end Aeneas.Std
