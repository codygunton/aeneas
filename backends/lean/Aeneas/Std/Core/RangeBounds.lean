module
public import Aeneas.Std.Primitives
public import Aeneas.Std.Range
public import Aeneas.Std.Core.Core
public section

@[expose] section

namespace Aeneas.Std

open Result

/-! `core::ops::range::Bound` and `core::ops::range::RangeBounds`. -/

@[rust_type "core::ops::range::Bound"]
inductive core.ops.range.Bound (T : Type u) where
| Included : T → core.ops.range.Bound T
| Excluded : T → core.ops.range.Bound T
| Unbounded : core.ops.range.Bound T

@[rust_trait "core::ops::range::RangeBounds"]
structure core.ops.range.RangeBounds (Self : Type _) (T : Type _) where
  start_bound : Self → Result (core.ops.range.Bound T)
  end_bound : Self → Result (core.ops.range.Bound T)

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFull, @T>}::start_bound"]
def core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds.start_bound
  (T : Type _) : core.ops.range.RangeFull → Result (core.ops.range.Bound T) :=
  fun _ => ok .Unbounded

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFull, @T>}::end_bound"]
def core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds.end_bound
  (T : Type _) : core.ops.range.RangeFull → Result (core.ops.range.Bound T) :=
  fun _ => ok .Unbounded

@[reducible, rust_trait_impl
  "core::ops::range::RangeBounds<core::ops::range::RangeFull, @T>"]
def core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds (T : Type _) :
  core.ops.range.RangeBounds core.ops.range.RangeFull T := {
  start_bound := core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds.start_bound T
  end_bound := core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds.end_bound T
}

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFrom<@T>, @T>}::start_bound"]
def core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound
  {T : Type _} : core.ops.range.RangeFrom T → Result (core.ops.range.Bound T) :=
  fun r => ok (.Included r.start)

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFrom<@T>, @T>}::end_bound"]
def core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound
  {T : Type _} : core.ops.range.RangeFrom T → Result (core.ops.range.Bound T) :=
  fun _ => ok .Unbounded

@[reducible, rust_trait_impl
  "core::ops::range::RangeBounds<core::ops::range::RangeFrom<@T>, @T>"]
def core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds (T : Type _) :
  core.ops.range.RangeBounds (core.ops.range.RangeFrom T) T := {
  start_bound := core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound
  end_bound := core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound
}

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeTo<@T>, @T>}::start_bound"]
def core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.start_bound
  {T : Type _} : core.ops.range.RangeTo T → Result (core.ops.range.Bound T) :=
  fun _ => ok .Unbounded

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeTo<@T>, @T>}::end_bound"]
def core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.end_bound
  {T : Type _} : core.ops.range.RangeTo T → Result (core.ops.range.Bound T) :=
  fun r => ok (.Excluded r.«end»)

@[reducible, rust_trait_impl
  "core::ops::range::RangeBounds<core::ops::range::RangeTo<@T>, @T>"]
def core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds (T : Type _) :
  core.ops.range.RangeBounds (core.ops.range.RangeTo T) T := {
  start_bound := core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.start_bound
  end_bound := core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.end_bound
}

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::Range<@T>, @T>}::start_bound"]
def core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.start_bound
  {T : Type _} : core.ops.range.Range T → Result (core.ops.range.Bound T) :=
  fun r => ok (.Included r.start)

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::Range<@T>, @T>}::end_bound"]
def core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.end_bound
  {T : Type _} : core.ops.range.Range T → Result (core.ops.range.Bound T) :=
  fun r => ok (.Excluded r.«end»)

@[reducible, rust_trait_impl
  "core::ops::range::RangeBounds<core::ops::range::Range<@T>, @T>"]
def core.ops.range.Range.Insts.CoreOpsRangeRangeBounds (T : Type _) :
  core.ops.range.RangeBounds (core.ops.range.Range T) T := {
  start_bound := core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.start_bound
  end_bound := core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.end_bound
}

/-- `RangeInclusive::end_bound`: `Excluded(end)` once exhausted, else `Included(end)`
    (`range.rs`, `impl RangeBounds<T> for RangeInclusive<T>`). -/
@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeInclusive<@T>, @T>}::start_bound"]
def core.ops.range.RangeInclusive.Insts.CoreOpsRangeRangeBounds.start_bound
  {T : Type _} : core.ops.range.RangeInclusive T → Result (core.ops.range.Bound T) :=
  fun r => ok (.Included r.start)

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeInclusive<@T>, @T>}::end_bound"]
def core.ops.range.RangeInclusive.Insts.CoreOpsRangeRangeBounds.end_bound
  {T : Type _} : core.ops.range.RangeInclusive T → Result (core.ops.range.Bound T) :=
  fun r => ok (if r.exhausted then .Excluded r.«end» else .Included r.«end»)

@[reducible, rust_trait_impl
  "core::ops::range::RangeBounds<core::ops::range::RangeInclusive<@T>, @T>"]
def core.ops.range.RangeInclusive.Insts.CoreOpsRangeRangeBounds (T : Type _) :
  core.ops.range.RangeBounds (core.ops.range.RangeInclusive T) T := {
  start_bound := core.ops.range.RangeInclusive.Insts.CoreOpsRangeRangeBounds.start_bound
  end_bound := core.ops.range.RangeInclusive.Insts.CoreOpsRangeRangeBounds.end_bound
}

end Aeneas.Std
