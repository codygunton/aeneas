module
public import Aeneas.Std.Core.IterModel
public import Aeneas.Std.Array.Array
public section

@[expose] section

/-! Iterator sources (`empty`, `once`, `repeat`, `Option::into_iter`, `[T; N]::into_iter`)
and the remaining `Range`/`RangeFrom` iterator methods (Rust 1.96). -/

namespace Aeneas.Std

open Result IterModel

/-! ## `core::iter::sources` -/

@[rust_type "core::iter::sources::empty::Empty" (body := .opaque)]
structure core.iter.sources.empty.Empty (T : Type u) : Type where
  mk ::

@[rust_fun "core::iter::sources::empty::empty"]
def core.iter.sources.empty.empty (T : Type _) : Result (core.iter.sources.empty.Empty T) :=
  ok ⟨⟩

@[rust_fun
  "core::iter::sources::empty::{core::iter::traits::iterator::Iterator<core::iter::sources::empty::Empty<@T>, @T>}::next"]
def core.iter.sources.empty.Empty.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type _} :
  core.iter.sources.empty.Empty T → Result ((Option T) × (core.iter.sources.empty.Empty T)) :=
  fun self => ok (none, self)

@[rust_fun
  "core::iter::sources::empty::{core::iter::traits::iterator::Iterator<core::iter::sources::empty::Empty<@T>, @T>}::size_hint"]
def core.iter.sources.empty.Empty.Insts.CoreIterTraitsIteratorIterator.size_hint
  {T : Type _} :
  core.iter.sources.empty.Empty T → Result (Std.Usize × (Option Std.Usize)) :=
  fun _ => ok (0#usize, some 0#usize)

/-- `option::IntoIter { inner: Item { opt } }`. -/
@[rust_type "core::option::IntoIter" (body := .opaque)]
structure core.option.IntoIter (A : Type u) where
  opt : Option A

@[rust_fun
  "core::option::{core::iter::traits::collect::IntoIterator<core::option::Option<@T>, @T, core::option::IntoIter<@T>>}::into_iter"]
def core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  {T : Type _} : Option T → Result (core.option.IntoIter T) :=
  fun o => ok ⟨o⟩

@[rust_fun
  "core::option::{core::iter::traits::iterator::Iterator<core::option::IntoIter<@A>, @A>}::next"]
def core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  {A : Type _} : core.option.IntoIter A → Result ((Option A) × (core.option.IntoIter A)) :=
  fun self => ok (self.opt, ⟨none⟩)

@[rust_fun
  "core::option::{core::iter::traits::double_ended::DoubleEndedIterator<core::option::IntoIter<@A>, @A>}::next_back"]
def core.option.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
  {A : Type _} : core.option.IntoIter A → Result ((Option A) × (core.option.IntoIter A)) :=
  fun self => ok (self.opt, ⟨none⟩)

@[rust_fun
  "core::option::{core::iter::traits::iterator::Iterator<core::option::IntoIter<@A>, @A>}::size_hint"]
def core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.size_hint
  {A : Type _} : core.option.IntoIter A → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    match self.opt with
    | none => ok (0#usize, some 0#usize)
    | some _ => ok (1#usize, some 1#usize)

/-- `Once { inner: option::IntoIter<T> }`. -/
@[rust_type "core::iter::sources::once::Once" (body := .opaque)]
structure core.iter.sources.once.Once (T : Type u) where
  inner : Option T

@[rust_fun "core::iter::sources::once::once"]
def core.iter.sources.once.once {T : Type _} : T → Result (core.iter.sources.once.Once T) :=
  fun x => ok ⟨some x⟩

@[rust_fun
  "core::iter::sources::once::{core::iter::traits::iterator::Iterator<core::iter::sources::once::Once<@T>, @T>}::next"]
def core.iter.sources.once.Once.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type _} : core.iter.sources.once.Once T → Result ((Option T) × (core.iter.sources.once.Once T)) :=
  fun self => ok (self.inner, ⟨none⟩)

@[rust_fun
  "core::iter::sources::once::{core::iter::traits::iterator::Iterator<core::iter::sources::once::Once<@T>, @T>}::size_hint"]
def core.iter.sources.once.Once.Insts.CoreIterTraitsIteratorIterator.size_hint
  {T : Type _} : core.iter.sources.once.Once T → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    match self.inner with
    | none => ok (0#usize, some 0#usize)
    | some _ => ok (1#usize, some 1#usize)

@[rust_type "core::iter::sources::repeat::Repeat" (body := .opaque)]
structure core.iter.sources.repeat.Repeat (A : Type u) where
  element : A

@[rust_fun "core::iter::sources::repeat::repeat"]
def core.iter.sources.repeat.repeat {T : Type _} (_cloneCloneInst : core.clone.Clone T) :
  T → Result (core.iter.sources.repeat.Repeat T) :=
  fun x => ok ⟨x⟩

@[rust_fun
  "core::iter::sources::repeat::{core::iter::traits::iterator::Iterator<core::iter::sources::repeat::Repeat<@A>, @A>}::next"]
def core.iter.sources.repeat.Repeat.Insts.CoreIterTraitsIteratorIterator.next
  {A : Type _} (cloneCloneInst : core.clone.Clone A) :
  core.iter.sources.repeat.Repeat A → Result ((Option A) × (core.iter.sources.repeat.Repeat A)) :=
  fun self => do
    let x ← cloneCloneInst.clone self.element
    ok (some x, self)

@[rust_fun
  "core::iter::sources::repeat::{core::iter::traits::iterator::Iterator<core::iter::sources::repeat::Repeat<@A>, @A>}::size_hint"]
def core.iter.sources.repeat.Repeat.Insts.CoreIterTraitsIteratorIterator.size_hint
  {A : Type _} (_cloneCloneInst : core.clone.Clone A) :
  core.iter.sources.repeat.Repeat A → Result (Std.Usize × (Option Std.Usize)) :=
  fun _ => ok (Usize.satOfNat Usize.max, none)

@[rust_fun
  "core::iter::sources::repeat::{core::iter::traits::iterator::Iterator<core::iter::sources::repeat::Repeat<@A>, @A>}::nth"]
def core.iter.sources.repeat.Repeat.Insts.CoreIterTraitsIteratorIterator.nth
  {A : Type _} (cloneCloneInst : core.clone.Clone A) :
  core.iter.sources.repeat.Repeat A → Std.Usize →
    Result ((Option A) × (core.iter.sources.repeat.Repeat A)) :=
  fun self _ => do
    let x ← cloneCloneInst.clone self.element
    ok (some x, self)

/-- `Repeat::last`: `panic!("iterator is infinite")`. -/
@[rust_fun
  "core::iter::sources::repeat::{core::iter::traits::iterator::Iterator<core::iter::sources::repeat::Repeat<@A>, @A>}::last"]
def core.iter.sources.repeat.Repeat.Insts.CoreIterTraitsIteratorIterator.last
  {A : Type _} (_cloneCloneInst : core.clone.Clone A) :
  core.iter.sources.repeat.Repeat A → Result (Option A) :=
  fun _ => fail .panic

/-- `Repeat::count`: `panic!("iterator is infinite")`. -/
@[rust_fun
  "core::iter::sources::repeat::{core::iter::traits::iterator::Iterator<core::iter::sources::repeat::Repeat<@A>, @A>}::count"]
def core.iter.sources.repeat.Repeat.Insts.CoreIterTraitsIteratorIterator.count
  {A : Type _} (_cloneCloneInst : core.clone.Clone A) :
  core.iter.sources.repeat.Repeat A → Result Std.Usize :=
  fun _ => fail .panic

/-! ## `[T; N]::into_iter` -/

/-- `array::IntoIter { data, alive }`: the elements still alive, in order. -/
@[rust_type "core::array::iter::IntoIter" (body := .opaque)]
structure core.array.iter.IntoIter (T : Type u) (N : Usize) where
  alive : List T

@[rust_fun
  "core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter"]
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  {T : Type _} {N : Std.Usize} : Array T N → Result (core.array.iter.IntoIter T N) :=
  fun a => ok ⟨a.val⟩

@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type _} {N : Std.Usize} :
  core.array.iter.IntoIter T N → Result ((Option T) × (core.array.iter.IntoIter T N)) :=
  fun self =>
    match self.alive with
    | [] => ok (none, self)
    | x :: xs => ok (some x, ⟨xs⟩)

@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::size_hint"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.size_hint
  {T : Type _} {N : Std.Usize} :
  core.array.iter.IntoIter T N → Result (Std.Usize × (Option Std.Usize)) :=
  fun self =>
    let n := Usize.satOfNat self.alive.length
    ok (n, some n)

@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::count"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.count
  {T : Type _} {N : Std.Usize} : core.array.iter.IntoIter T N → Result Std.Usize :=
  fun self => ok (Usize.satOfNat self.alive.length)

/-- `array::IntoIter::last`: `self.next_back()`. -/
@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::last"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.last
  {T : Type _} {N : Std.Usize} : core.array.iter.IntoIter T N → Result (Option T) :=
  fun self => ok self.alive.getLast?

@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::fold"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
  {T : Type _} {Acc : Type _} {Fold : Type _} {N : Std.Usize}
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × T) Acc) :
  core.array.iter.IntoIter T N → Acc → Fold → Result Acc :=
  fun self acc f => do
    let (acc, _) ← foldNext core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
      self (acc, f) (fun (acc, f) x => opsfunctionFnMutFoldPairAccInst.call_mut f (acc, x))
    ok acc

/-! ## `Range` / `RangeFrom` -/

/-- `self.start = self.end.clone(); None` (the exhausting branch of `Range::nth`). -/
def core.ops.range.Range.nthExhaust {A : Type _} (StepInst : core.iter.range.Step A)
    (self : core.ops.range.Range A) : Result ((Option A) × (core.ops.range.Range A)) := do
  let e ← StepInst.cloneInst.clone self.«end»
  ok (none, { self with start := e })

/-- `Range::nth` (`spec_nth`). -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::nth"]
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.nth
  {A : Type _} (StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Std.Usize → Result ((Option A) × (core.ops.range.Range A)) :=
  fun self n => do
    let s ← StepInst.cloneInst.clone self.start
    let plus ← StepInst.forward_checked s n
    match plus with
    | none => core.ops.range.Range.nthExhaust StepInst self
    | some p => do
      let lt ← StepInst.partialOrdInst.lt p self.«end»
      if lt then do
        let p' ← StepInst.cloneInst.clone p
        let next ← StepInst.forward_checked p' 1#usize
        match next with
        | none => fail .panic
        | some s' => ok (some p, { self with start := s' })
      else core.ops.range.Range.nthExhaust StepInst self

/-- `Range::count`: `steps_between(start, end).1.expect("count overflowed usize")` when
    `start < end`, else `0`. -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::count"]
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.count
  {A : Type _} (StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Result Std.Usize :=
  fun self => do
    let lt ← StepInst.partialOrdInst.lt self.start self.«end»
    if lt then do
      let (_, hi) ← StepInst.steps_between self.start self.«end»
      match hi with
      | some n => ok n
      | none => fail .panic
    else ok 0#usize

/-- `Range::last`: `self.next_back()`. -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::last"]
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.last
  {A : Type _} (StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Result (Option A) :=
  fun self => do
    let (o, _) ← core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back StepInst self
    ok o

/-- `Range::max`: `self.next_back()`. -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::max"]
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.max
  {A : Type _} (StepInst : core.iter.range.Step A) (_cmpOrdInst : core.cmp.Ord A) :
  core.ops.range.Range A → Result (Option A) :=
  fun self => do
    let (o, _) ← core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back StepInst self
    ok o

/-- `RangeFrom::next`: `let n = Step::forward(self.start.clone(), 1);
    Some(mem::replace(&mut self.start, n))`; `Step::forward` overflows (panics with overflow
    checks). -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeFrom<@A>, @A>}::next"]
def core.ops.range.RangeFrom.Insts.CoreIterTraitsIteratorIterator.next
  {A : Type _} (StepInst : core.iter.range.Step A) :
  core.ops.range.RangeFrom A → Result ((Option A) × (core.ops.range.RangeFrom A)) :=
  fun self => do
    let s ← StepInst.cloneInst.clone self.start
    let n ← StepInst.forward_checked s 1#usize
    match n with
    | none => fail .integerOverflow
    | some n => ok (some self.start, ⟨n⟩)

/-- `RangeFrom::size_hint`: `(usize::MAX, None)`. -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeFrom<@A>, @A>}::size_hint"]
def core.ops.range.RangeFrom.Insts.CoreIterTraitsIteratorIterator.size_hint
  {A : Type _} (_StepInst : core.iter.range.Step A) :
  core.ops.range.RangeFrom A → Result (Std.Usize × (Option Std.Usize)) :=
  fun _ => ok (Usize.satOfNat Usize.max, none)

end Aeneas.Std
