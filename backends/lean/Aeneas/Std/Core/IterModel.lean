module
public import Aeneas.Std.Core.Iter
public section

@[expose] section

/-! Executable building blocks for the iterator models: everything is expressed through
`next` / `next_back` of the underlying iterator, in the order the standard library calls
them (Rust 1.96 `core::iter`). The default `Iterator` methods (`fold`, `nth`, `advance_by`,
`try_fold`, ...) all reduce to repeated `next` calls; specialised overrides in `std` that
skip `next` calls only do so on iterators without side effects, so they are not
distinguishable from these definitions. -/

namespace Aeneas.Std.IterModel

open Result

/-- `and_then_or_clear(opt, f)` (`core::iter::adapters`): apply `f` to the contained value and
    clear the option when `f` returns `None`. -/
def andThenOrClear {T : Type u} {U : Type v} (opt : Option T) (f : T → Result (Option U × T)) :
    Result (Option U × Option T) :=
  match opt with
  | none => ok (none, none)
  | some t => do
    let (x, t) ← f t
    match x with
    | none => ok (none, none)
    | some x => ok (some x, some t)

/-- Fold with a `next` function: `while let Some(x) = self.next() { s = step(s, x) }`. -/
def foldNext {I : Type u} {Item : Type v} {σ : Type w}
    (next : I → Result (Option Item × I)) (it : I) (s : σ) (step : σ → Item → Result σ) :
    Result σ := do
  let (o, it) ← next it
  match o with
  | none => ok s
  | some x => do
    let s ← step s x
    foldNext next it s step
partial_fixpoint

/-- Short-circuiting fold (`try_fold`): stops at the first `.inr`, returning the iterator
    state right after the element that stopped it. -/
def tryFoldNext {I : Type u} {Item : Type v} {σ : Type w} {β : Type x}
    (next : I → Result (Option Item × I)) (it : I) (s : σ)
    (step : σ → Item → Result (σ ⊕ β)) : Result ((σ ⊕ β) × I) := do
  let (o, it) ← next it
  match o with
  | none => ok (.inl s, it)
  | some x => do
    let r ← step s x
    match r with
    | .inl s => tryFoldNext next it s step
    | .inr b => ok (.inr b, it)
partial_fixpoint

/-- Collects the remaining items (in order). -/
def toListNext {I : Type u} {Item : Type v} (next : I → Result (Option Item × I)) (it : I) :
    Result (List Item) := do
  let xs ← foldNext next it ([] : List Item) (fun acc x => ok (x :: acc))
  ok xs.reverse

/-- Default `advance_by`: calls `next` up to `n` times; returns the number of steps that
    could not be taken (`0` is `Ok(())`). -/
def advanceByNext {I : Type u} {Item : Type v} (next : I → Result (Option Item × I)) (it : I) :
    Nat → Result (Nat × I)
  | 0 => ok (0, it)
  | n + 1 => do
    let (o, it) ← next it
    match o with
    | none => ok (n + 1, it)
    | some _ => advanceByNext next it n

/-- Default `nth`: `self.advance_by(n).ok()?; self.next()`. -/
def nthNext {I : Type u} {Item : Type v} (next : I → Result (Option Item × I)) (it : I)
    (n : Nat) : Result (Option Item × I) := do
  let (k, it) ← advanceByNext next it n
  if k = 0 then next it else ok (none, it)

/-- Default `count`: `fold(0, |c, _| c + 1)` (overflow checked). -/
def countNext {I : Type u} {Item : Type v} (next : I → Result (Option Item × I)) (it : I) :
    Result Usize :=
  foldNext next it 0#usize (fun c _ => c + 1#usize)

/-- Default `last`: `fold(None, |_, x| Some(x))`. -/
def lastNext {I : Type u} {Item : Type v} (next : I → Result (Option Item × I)) (it : I) :
    Result (Option Item) :=
  foldNext next it none (fun _ x => ok (some x))

/-- Default `find`: the first item satisfying the predicate (closure state threaded). -/
def findNext {I : Type u} {Item : Type v} {P : Type w}
    (next : I → Result (Option Item × I)) (call : P → Item → Result (Bool × P))
    (it : I) (p : P) : Result (Option Item × I × P) := do
  let (r, it) ← tryFoldNext next it p (fun p x => do
    let (b, p) ← call p x
    if b then ok (.inr (x, p)) else ok (.inl p))
  match r with
  | .inl p => ok (none, it, p)
  | .inr (x, p) => ok (some x, it, p)

/-- Default `find_map`. -/
def findMapNext {I : Type u} {Item : Type v} {P : Type w} {B : Type x}
    (next : I → Result (Option Item × I)) (call : P → Item → Result (Option B × P))
    (it : I) (p : P) : Result (Option B × I × P) := do
  let (r, it) ← tryFoldNext next it p (fun p x => do
    let (b, p) ← call p x
    match b with
    | some b => ok (.inr (b, p))
    | none => ok (.inl p))
  match r with
  | .inl p => ok (none, it, p)
  | .inr (b, p) => ok (some b, it, p)

/-- `ExactSizeIterator::len` default: `size_hint` must be exact (`assert_eq!`). -/
def lenOfHint (hint : Result (Usize × Option Usize)) : Result Usize := do
  let (lo, hi) ← hint
  match hi with
  | some h => if h.val = lo.val then ok lo else fail .panic
  | none => fail .panic

/-- Item from the back obtained through a forward iterator instance of the same Rust type:
    the forward view (on a copy) gives the value, the `next_back` call gives the new state.
    Used where the Lean signature has two (Rust-equal) item types for the two directions. -/
def backViaForward {U : Type u} {Item : Type v} {Item' : Type w}
    (next : U → Result (Option Item × U)) (nextBack : U → Result (Option Item' × U)) (u : U) :
    Result (Option Item × U) := do
  let xs ← toListNext next u
  let (o, u') ← nextBack u
  match o with
  | none => ok (none, u')
  | some _ => ok (xs.getLast?, u')

/-- `FlattenCompat::next` (`flatten.rs`): `outer` is the fused outer iterator (already mapped
    to inner iterators), `front`/`back` are `frontiter`/`backiter`. -/
def flatNext {O : Type u} {U : Type v} {Item : Type w}
    (outerNext : O → Result (Option U × O)) (innerNext : U → Result (Option Item × U))
    (outer : Option O) (front back : Option U) :
    Result (Option Item × Option O × Option U × Option U) := do
  let (r, front) ← andThenOrClear front innerNext
  match r with
  | some x => ok (some x, outer, front, back)
  | none => do
    let (o, outer) ← andThenOrClear outer outerNext
    match o with
    | none => do
      let (r, back) ← andThenOrClear back innerNext
      ok (r, outer, front, back)
    | some u => flatNext outerNext innerNext outer (some u) back
partial_fixpoint

/-- `FlattenCompat::next_back`. -/
def flatNextBack {O : Type u} {U : Type v} {Item : Type w}
    (outerNextBack : O → Result (Option U × O)) (innerNextBack : U → Result (Option Item × U))
    (outer : Option O) (front back : Option U) :
    Result (Option Item × Option O × Option U × Option U) := do
  let (r, back) ← andThenOrClear back innerNextBack
  match r with
  | some x => ok (some x, outer, front, back)
  | none => do
    let (o, outer) ← andThenOrClear outer outerNextBack
    match o with
    | none => do
      let (r, front) ← andThenOrClear front innerNextBack
      ok (r, outer, front, back)
    | some u => flatNextBack outerNextBack innerNextBack outer front (some u)
partial_fixpoint

/-- `FlattenCompat::iter_fold`: folds over the inner iterators (front, outer..., back). -/
def flatIterFold {O : Type u} {U : Type v} {σ : Type w}
    (outerNext : O → Result (Option U × O)) (outer : Option O) (front back : Option U)
    (s : σ) (step : σ → U → Result σ) : Result σ := do
  let s ← match front with
    | none => ok s
    | some f => step s f
  let s ← match outer with
    | none => ok s
    | some o => foldNext outerNext o s step
  match back with
  | none => ok s
  | some b => step s b

/-- `FlattenCompat::size_hint` (generic impl; the `OneShot`/`ConstSizeIntoIterator`
    specialisations are not distinguished). -/
def flatSizeHint {U : Type v}
    (outerHint : Result (Usize × Option Usize)) (innerHint : U → Result (Usize × Option Usize))
    (front back : Option U) : Result (Usize × Option Usize) := do
  let (flo, fhi) ← match front with
    | none => ok (0#usize, some 0#usize)
    | some f => innerHint f
  let (blo, bhi) ← match back with
    | none => ok (0#usize, some 0#usize)
    | some b => innerHint b
  let lo := Usize.satOfNat (flo.val + blo.val)
  let (olo, ohi) ← outerHint
  match ohi, fhi, bhi with
  | some h, some a, some b =>
    if olo.val = 0 ∧ h.val = 0 then ok (lo, Usize.checkedOfNat (a.val + b.val))
    else ok (lo, none)
  | _, _, _ => ok (lo, none)

end Aeneas.Std.IterModel
