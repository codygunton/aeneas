/- `alloc::rc::Rc` and `alloc::sync::Arc`.

Both are modelled as plain values: the extracted code never mutates through a shared `Rc`/`Arc`
(no interior mutability is modelled), so sharing is unobservable, except for the reference count.
Reference counts are not tracked: `Rc::get_mut` always succeeds. This matches Rust whenever the
`Rc` is unique, which is the only case the extracted code relies on (regalloc2's
`Bump::get_mut(..).expect("we dropped all refs to this")`); on a shared `Rc`, Rust returns
`None` instead. -/
module
public import Aeneas.Std.Alloc.AllocatorClone
public import Aeneas.Std.Core.Default
public section

namespace Aeneas.Std

open Result

@[rust_type "alloc::rc::Rc" (body := .opaque)]
structure alloc.rc.Rc (T : Type u) where
  val : T

@[rust_type "alloc::sync::Arc" (body := .opaque)]
structure alloc.sync.Arc (T : Type u) where
  val : T

/-- Output: (`Some` of the contents, backward function writing them back). -/
@[expose, rust_fun "alloc::rc::{alloc::rc::Rc<@T>}::get_mut"]
def alloc.rc.Rc.get_mut {T : Type _} (A : Type _) (r : alloc.rc.Rc T) :
    Result ((Option T) × (Option T → alloc.rc.Rc T)) :=
  ok (some r.val, fun o => match o with | some x => { val := x } | none => r)

@[expose, rust_fun "alloc::rc::{core::ops::deref::Deref<alloc::rc::Rc<@T>, @T>}::deref"]
def alloc.rc.Rc.Insts.CoreOpsDerefDeref.deref {T : Type _} (A : Type _) (r : alloc.rc.Rc T) :
    Result T :=
  ok r.val

@[expose, rust_fun "alloc::rc::{core::clone::Clone<alloc::rc::Rc<@T>>}::clone"]
def alloc.rc.Rc.Insts.CoreCloneClone.clone {T : Type _} {A : Type _}
    (_allocInst : core.alloc.AllocatorClone A) (r : alloc.rc.Rc T) : Result (alloc.rc.Rc T) :=
  ok r

/-- `Rc::new(T::default())`. -/
@[expose, rust_fun "alloc::rc::{core::default::Default<alloc::rc::Rc<@T>>}::default"]
def alloc.rc.Rc.Insts.CoreDefaultDefault.default {T : Type _}
    (defaultInst : core.default.Default T) : Result (alloc.rc.Rc T) := do
  let x ← defaultInst.default
  ok { val := x }

@[expose, rust_fun "alloc::sync::{alloc::sync::Arc<@T>}::new"]
def alloc.sync.Arc.new {T : Type _} (x : T) : Result (alloc.sync.Arc T) :=
  ok { val := x }

end Aeneas.Std
