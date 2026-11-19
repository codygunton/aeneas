/- `alloc::collections::vec_deque::VecDeque`: a FIFO queue. The logical contents are
`front ++ back.reverse`. -/
module
public import Aeneas.Std.Alloc.Util
public import Aeneas.Std.Alloc.Alloc
public section

namespace Aeneas.Std

open Result

@[rust_type "alloc::collections::vec_deque::VecDeque" (body := .opaque)]
structure alloc.collections.vec_deque.VecDeque (T : Type u) (A : Type v) where
  front : List T
  back : List T

@[expose, rust_fun
  "alloc::collections::vec_deque::{core::default::Default<alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>>}::default"]
def alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreDefaultDefault.default (T : Type _) :
    Result (alloc.collections.vec_deque.VecDeque T alloc.alloc.Global) :=
  ok { front := [], back := [] }

@[expose, rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::pop_front"]
def alloc.collections.vec_deque.VecDeque.pop_front {T : Type _} {A : Type _}
    (q : alloc.collections.vec_deque.VecDeque T A) :
    Result ((Option T) × (alloc.collections.vec_deque.VecDeque T A)) :=
  match q.front with
  | x :: front => ok (some x, { q with front })
  | [] =>
    match q.back.reverse with
    | [] => ok (none, q)
    | x :: front => ok (some x, { front, back := [] })

/-- Rust's "capacity overflow" panic (past `isize::MAX` bytes) is unreachable for a
    materialised queue and is not modelled. -/
@[expose, rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::push_back"]
def alloc.collections.vec_deque.VecDeque.push_back {T : Type _} {A : Type _}
    (q : alloc.collections.vec_deque.VecDeque T A) (x : T) :
    Result (alloc.collections.vec_deque.VecDeque T A) :=
  ok { q with back := x :: q.back }
