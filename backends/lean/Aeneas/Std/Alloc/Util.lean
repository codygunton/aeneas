/- Small executable helpers shared by the `alloc`/`std` collection models. -/
module
public import Aeneas.Std.Alloc.Vec
public import Aeneas.Std.Core.Iter
public section

namespace Aeneas.Std.AllocModel

open Result

/-- A `usize` from a natural number; overflow is a failure. -/
@[expose] def usize (n : Nat) : Result Usize :=
  if h : n ≤ Usize.max then ok (Usize.ofNatCore n (by scalar_tac)) else fail .integerOverflow

/-- A `Slice` from a list; exceeding the maximum size is a failure. -/
@[expose] def slice {α : Type u} (l : List α) : Result (Slice α) :=
  if h : l.length ≤ Usize.max then ok (Slice.from l h) else fail .maximumSizeExceeded

/-- A `Vec` from a list; exceeding the maximum size is a failure (Rust: capacity overflow). -/
@[expose] def vec {α : Type u} (l : List α) : Result (alloc.vec.Vec α) := do
  let s ← slice l
  ok { slice := s }

/-- Exact size hint of an iterator that knows its remaining length. -/
@[expose] def exactSizeHint (n : Nat) : Result (Usize × Option Usize) := do
  let n ← usize n
  ok (n, some n)

/-- Drain an iterator, collecting the items it yields in order. -/
@[expose] def iterToList {I : Type u} {T : Type v}
    (iterInst : core.iter.traits.iterator.Iterator I T) (it : I) (acc : List T) :
    Result (List T) := do
  let (o, it) ← iterInst.next it
  match o with
  | none => ok acc.reverse
  | some x => iterToList iterInst it (x :: acc)
partial_fixpoint

/-- `xs[i] := x` (no-op out of bounds). -/
@[expose] def setAt {α : Type u} (xs : List α) (i : Nat) (x : α) : List α := xs.set i x

/-- Lexicographic comparison of two lists with `cmp` (Rust `SliceOrd::compare`). -/
@[expose] def lexCmp {α : Type u} (cmp : α → α → Result Ordering) :
    List α → List α → Result Ordering
  | [], [] => ok .eq
  | [], _ :: _ => ok .lt
  | _ :: _, [] => ok .gt
  | x :: xs, y :: ys => do
    let c ← cmp x y
    match c with
    | .eq => lexCmp cmp xs ys
    | o => ok o

/-- Call the predicate once on every element, in order; keep the elements it accepts. -/
@[expose] def retainList {T : Type u} {F : Type v} (call : F → T → Result (Bool × F)) (f : F)
    (acc : List T) : List T → Result (List T)
  | [] => ok acc.reverse
  | x :: xs => do
    let (keep, f) ← call f x
    if keep then retainList call f (x :: acc) xs else retainList call f acc xs

/-- `Iterator::fold` over the remaining elements, in order. -/
@[expose] def foldList {T : Type u} {B : Type v} {F : Type w} (call : F → B × T → Result (B × F))
    (f : F) (acc : B) : List T → Result B
  | [] => ok acc
  | x :: xs => do
    let (acc, f) ← call f (acc, x)
    foldList call f acc xs

end Aeneas.Std.AllocModel
