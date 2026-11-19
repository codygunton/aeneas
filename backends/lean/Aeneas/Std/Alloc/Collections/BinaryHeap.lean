/- `alloc::collections::binary_heap::BinaryHeap`: the Rust 1.96 algorithm (`sift_up`,
`sift_down_to_bottom`) on the backing array, with the same comparisons (`PartialOrd::le`) in the
same order, so the pop order (including among equal elements) is exactly Rust's. -/
module
public import Aeneas.Std.Alloc.Util
public import Aeneas.Std.Alloc.Alloc
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Default
public section

namespace Aeneas.Std

open Result

@[rust_type "alloc::collections::binary_heap::BinaryHeap" (body := .opaque)]
structure alloc.collections.binary_heap.BinaryHeap (T : Type u) (A : Type v) where
  data : _root_.Array T

namespace BinaryHeapModel

@[expose] def get {T : Type u} (a : _root_.Array T) (i : Nat) : Result T :=
  match a[i]? with
  | some x => ok x
  | none => fail .panic

/-- `sift_up` loop: `elem` is the element in the hole at `hole`. Returns the final array and
    hole position. -/
@[expose] def siftUpLoop {T : Type u} (le : T → T → Result Bool) (start : Nat) (elem : T)
    (a : _root_.Array T) (hole : Nat) : Result (_root_.Array T × Nat) :=
  if _h : hole > start then do
    let parent := (hole - 1) / 2
    let p ← get a parent
    let b ← le elem p
    if b then ok (a.set! hole elem, hole)
    else siftUpLoop le start elem (a.set! hole p) parent
  else ok (a.set! hole elem, hole)
termination_by hole
decreasing_by omega

@[expose] def siftUp {T : Type u} (le : T → T → Result Bool) (start pos : Nat)
    (a : _root_.Array T) : Result (_root_.Array T × Nat) := do
  let elem ← get a pos
  siftUpLoop le start elem a pos

/-- `sift_down_to_bottom` loop, with `endN = len` and the element `elem` in the hole. -/
@[expose] def siftDownLoop {T : Type u} (le : T → T → Result Bool) (endN start : Nat) (elem : T)
    (a : _root_.Array T) (hole : Nat) : Result (_root_.Array T) :=
  let child := 2 * hole + 1
  if child ≤ endN - 2 then do
    let c1 ← get a child
    let c2 ← get a (child + 1)
    let b ← le c1 c2
    let child' := if b then child + 1 else child
    let cv ← get a child'
    siftDownLoop le endN start elem (a.set! hole cv) child'
  else do
    let (a, hole) ←
      if child = endN - 1 then do
        let cv ← get a child
        ok (a.set! hole cv, child)
      else ok (a, hole)
    let (a, _) ← siftUpLoop le start elem a hole
    ok a
partial_fixpoint

@[expose] def siftDownToBottom {T : Type u} (le : T → T → Result Bool) (pos : Nat)
    (a : _root_.Array T) : Result (_root_.Array T) := do
  let elem ← get a pos
  siftDownLoop le a.size pos elem a pos

end BinaryHeapModel

open BinaryHeapModel

@[expose, rust_fun
  "alloc::collections::binary_heap::{core::default::Default<alloc::collections::binary_heap::BinaryHeap<@T, alloc::alloc::Global>>}::default"]
def alloc.collections.binary_heap.BinaryHeapTGlobal.Insts.CoreDefaultDefault.default (T : Type _) :
    Result (alloc.collections.binary_heap.BinaryHeap T alloc.alloc.Global) :=
  ok { data := #[] }

@[expose, rust_fun
  "alloc::collections::binary_heap::{alloc::collections::binary_heap::BinaryHeap<@T, @A>}::pop"]
def alloc.collections.binary_heap.BinaryHeap.pop {T : Type _} {A : Type _}
    (ordInst : core.cmp.Ord T) (h : alloc.collections.binary_heap.BinaryHeap T A) :
    Result ((Option T) × (alloc.collections.binary_heap.BinaryHeap T A)) :=
  match h.data.back? with
  | none => ok (none, h)
  | some item =>
    let a := h.data.pop
    if a.isEmpty then ok (some item, { data := a })
    else do
      let top ← get a 0
      let a ← siftDownToBottom ordInst.partialOrdInst.le 0 (a.set! 0 item)
      ok (some top, { data := a })

@[expose, rust_fun
  "alloc::collections::binary_heap::{alloc::collections::binary_heap::BinaryHeap<@T, @A>}::push"]
def alloc.collections.binary_heap.BinaryHeap.push {T : Type _} {A : Type _}
    (ordInst : core.cmp.Ord T) (h : alloc.collections.binary_heap.BinaryHeap T A) (item : T) :
    Result (alloc.collections.binary_heap.BinaryHeap T A) := do
  let oldLen := h.data.size
  if oldLen + 1 > Isize.max then fail .panic
  else
    let (a, _) ← siftUp ordInst.partialOrdInst.le 0 oldLen (h.data.push item)
    ok { data := a }

@[expose, rust_fun
  "alloc::collections::binary_heap::{alloc::collections::binary_heap::BinaryHeap<@T, @A>}::peek"]
def alloc.collections.binary_heap.BinaryHeap.peek {T : Type _} {A : Type _}
    (h : alloc.collections.binary_heap.BinaryHeap T A) : Result (Option T) :=
  ok h.data[0]?

@[expose, rust_fun
  "alloc::collections::binary_heap::{alloc::collections::binary_heap::BinaryHeap<@T, @A>}::len"]
def alloc.collections.binary_heap.BinaryHeap.len {T : Type _} {A : Type _}
    (h : alloc.collections.binary_heap.BinaryHeap T A) : Result Usize :=
  AllocModel.usize h.data.size

@[expose, rust_fun
  "alloc::collections::binary_heap::{alloc::collections::binary_heap::BinaryHeap<@T, @A>}::is_empty"]
def alloc.collections.binary_heap.BinaryHeap.is_empty {T : Type _} {A : Type _}
    (h : alloc.collections.binary_heap.BinaryHeap T A) : Result Bool :=
  ok h.data.isEmpty

@[expose, rust_fun
  "alloc::collections::binary_heap::{alloc::collections::binary_heap::BinaryHeap<@T, @A>}::clear"]
def alloc.collections.binary_heap.BinaryHeap.clear {T : Type _} {A : Type _}
    (_ : alloc.collections.binary_heap.BinaryHeap T A) :
    Result (alloc.collections.binary_heap.BinaryHeap T A) :=
  ok { data := #[] }

end Aeneas.Std
