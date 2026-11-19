/- `alloc::slice`: `sort_by_key`, `join` and the `Join` trait. -/
module
public import Aeneas.Std.Alloc.Util
public import Aeneas.Std.Core.Cmp
public section

namespace Aeneas.Std

open Result

@[rust_trait "alloc::slice::Join"]
structure alloc.slice.Join (Self : Type _) (Separator : Type _) (Self_Output : Type _) where
  join : Self → Separator → Result Self_Output

namespace SortModel

variable {T : Type u} {F : Type v}

/-- Insert `x` into the sorted prefix given in reverse (`p_{i-1} :: p_{i-2} :: ...`), comparing
    `is_less(x, p)` from the right as Rust's `insert_tail`. `moved` collects the elements that
    move one position right. -/
@[expose] def insertTail (isLess : F → T → T → Result (Bool × F)) (f : F) (x : T)
    (moved : List T) : List T → Result (List T × F)
  | [] => ok (moved.reverse ++ [x], f)
  | p :: rest => do
    let (lt, f) ← isLess f x p
    if lt then insertTail isLess f x (p :: moved) rest
    else ok (moved.reverse ++ x :: p :: rest, f)

/-- `insertion_sort_shift_left(v, 1, is_less)`; the prefix is kept reversed. -/
@[expose] def insertionSort (isLess : F → T → T → Result (Bool × F)) (f : F) (accRev : List T) :
    List T → Result (List T × F)
  | [] => ok (accRev.reverse, f)
  | x :: xs => do
    match accRev with
    | [] => insertionSort isLess f [x] xs
    | _ =>
      let (accRev, f) ← insertTail isLess f x [] accRev
      insertionSort isLess f accRev xs

/-- Stable merge: an element of `r` goes first only if it is strictly less. -/
@[expose] def merge {T : Type u} {F : Type v} (isLess : F → T → T → Result (Bool × F)) (f : F)
    (l r : List T) : Result (List T × F) :=
  match l, r with
  | [], ys => ok (ys, f)
  | x :: xs, [] => ok (x :: xs, f)
  | x :: xs, y :: ys =>
    bind (isLess f y x) fun p =>
      if p.1 then bind (merge isLess p.2 (x :: xs) ys) fun q => ok (y :: q.1, q.2)
      else bind (merge isLess p.2 xs (y :: ys)) fun q => ok (x :: q.1, q.2)
partial_fixpoint

@[expose] def mergeSort {T : Type u} {F : Type v} (isLess : F → T → T → Result (Bool × F))
    (f : F) (l : List T) : Result (List T × F) :=
  if l.length < 2 then ok (l, f)
  else
    bind (mergeSort isLess f (l.take (l.length / 2))) fun a =>
    bind (mergeSort isLess a.2 (l.drop (l.length / 2))) fun b =>
    merge isLess b.2 a.1 b.1
partial_fixpoint

end SortModel

/-- Stable sort by key, `is_less(a, b) = f(a) < f(b)` (`PartialOrd::lt` of `K`). Slices of at
    most 20 elements use Rust's insertion sort (same comparisons in the same order); longer ones
    use a stable merge sort, which gives the same result (a stable sort's output is unique) but
    calls the key function in a different sequence than Rust's driftsort (only observable with
    a stateful key function). -/
@[expose, rust_fun "alloc::slice::{[@T]}::sort_by_key"]
def alloc.slice.Slice.sort_by_key {T : Type _} {K : Type _} {F : Type _}
    (fnInst : core.ops.function.FnMut F T K) (ordK : core.cmp.Ord K) (s : Slice T) (f : F) :
    Result (Slice T) := do
  let isLess := fun (f : F) (a b : T) => do
    let (ka, f) ← fnInst.call_mut f a
    let (kb, f) ← fnInst.call_mut f b
    let lt ← ordK.partialOrdInst.lt ka kb
    ok (lt, f)
  let (l, _) ←
    if s.val.length ≤ 20 then SortModel.insertionSort isLess f [] s.val
    else SortModel.mergeSort isLess f s.val
  AllocModel.slice l

@[expose, rust_fun "alloc::slice::{[@T]}::join"]
def alloc.slice.Slice.join {T : Type _} {Separator : Type _} {Clause0_Output : Type _}
    (joinInst : alloc.slice.Join (Slice T) Separator Clause0_Output) (s : Slice T)
    (sep : Separator) : Result Clause0_Output :=
  joinInst.join s sep

end Aeneas.Std
