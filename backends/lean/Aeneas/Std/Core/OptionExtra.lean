module
public import Aeneas.Std.Core.CoreOption
public import Aeneas.Std.Core.CoreResult
public import Aeneas.Std.Core.Default
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.String
public section

@[expose] section

/-! `core::option` / `core::result` / `bool` methods (Rust 1.96). -/

namespace Aeneas.Std

open Result

/-! ## `Option` -/

@[rust_fun "core::option::{core::option::Option<@T>}::as_ref"]
def core.option.Option.as_ref {T : Type _} : Option T → Result (Option T) :=
  fun o => ok o

@[rust_fun "core::option::{core::option::Option<@T>}::as_mut"]
def core.option.Option.as_mut {T : Type _} : Option T → Result ((Option T) × (Option T → Option T)) :=
  fun o => ok (o, fun o' => match o with
    | none => none
    | some _ => o')

@[rust_fun "core::option::{core::option::Option<@T>}::unwrap_or_else"]
def core.option.Option.unwrap_or_else {T : Type _} {F : Type _}
  (opsfunctionFnOnceFTupleTInst : core.ops.function.FnOnce F Unit T) : Option T → F → Result T :=
  fun o f => match o with
    | some x => ok x
    | none => opsfunctionFnOnceFTupleTInst.call_once f ()

@[rust_fun "core::option::{core::option::Option<@T>}::unwrap_or_default"]
def core.option.Option.unwrap_or_default {T : Type _}
  (defaultDefaultInst : core.default.Default T) : Option T → Result T :=
  fun o => match o with
    | some x => ok x
    | none => defaultDefaultInst.default

@[rust_fun "core::option::{core::option::Option<@T>}::map_or"]
def core.option.Option.map_or {T : Type _} {U : Type _} {F : Type _}
  (opsfunctionFnOnceFTupleTUInst : core.ops.function.FnOnce F T U) : Option T → U → F → Result U :=
  fun o d f => match o with
    | some x => opsfunctionFnOnceFTupleTUInst.call_once f x
    | none => ok d

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or_else"]
def core.option.Option.ok_or_else {T : Type _} {E : Type _} {F : Type _}
  (opsfunctionFnOnceFTupleEInst : core.ops.function.FnOnce F Unit E) :
  Option T → F → Result (core.result.Result T E) :=
  fun o f => match o with
    | some x => ok (.Ok x)
    | none => do
      let e ← opsfunctionFnOnceFTupleEInst.call_once f ()
      ok (.Err e)

@[rust_fun "core::option::{core::option::Option<@T>}::and_then"]
def core.option.Option.and_then {T : Type _} {U : Type _} {F : Type _}
  (opsfunctionFnOnceFTupleTOptionInst : core.ops.function.FnOnce F T (Option U)) :
  Option T → F → Result (Option U) :=
  fun o f => match o with
    | some x => opsfunctionFnOnceFTupleTOptionInst.call_once f x
    | none => ok none

/-- `filter`: `if let Some(x) = self { if predicate(&x) { return Some(x) } } None`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::filter"]
def core.option.Option.filter {T : Type _} {P : Type _}
  (opsfunctionFnOncePTupleSharedTBoolInst : core.ops.function.FnOnce P T Bool) :
  Option T → P → Result (Option T) :=
  fun o p => match o with
    | some x => do
      let b ← opsfunctionFnOncePTupleSharedTBoolInst.call_once p x
      ok (if b then some x else none)
    | none => ok none

@[rust_fun "core::option::{core::option::Option<@T>}::or"]
def core.option.Option.or {T : Type _} : Option T → Option T → Result (Option T) :=
  fun o other => match o with
    | some x => ok (some x)
    | none => ok other

@[rust_fun "core::option::{core::option::Option<@T>}::or_else"]
def core.option.Option.or_else {T : Type _} {F : Type _}
  (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T)) :
  Option T → F → Result (Option T) :=
  fun o f => match o with
    | some x => ok (some x)
    | none => opsfunctionFnOnceFTupleOptionInst.call_once f ()

/-- `insert`: `*self = Some(value); self.as_mut().unwrap()`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::insert"]
def core.option.Option.insert {T : Type _} : Option T → T → Result (T × (T → Option T)) :=
  fun _ v => ok (v, fun v => some v)

/-- `get_or_insert`: inserts `value` when `None`, then returns a mutable borrow of the
    contents. -/
@[rust_fun "core::option::{core::option::Option<@T>}::get_or_insert"]
def core.option.Option.get_or_insert {T : Type _} : Option T → T → Result (T × (T → Option T)) :=
  fun o v => match o with
    | some x => ok (x, fun v => some v)
    | none => ok (v, fun v => some v)

/-- `replace`: `mem::replace(self, Some(value))`; returns the old value and the new `self`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::replace"]
def core.option.Option.replace {T : Type _} : Option T → T → Result ((Option T) × (Option T)) :=
  fun o v => ok (o, some v)

/-- `Option<&T>::copied`. -/
@[rust_fun "core::option::{core::option::Option<&'0 @T>}::copied"]
def core.option.OptionShared0T.copied {T : Type _} (_markerCopyInst : core.marker.Copy T) :
  Option T → Result (Option T) :=
  fun o => ok o

/-- `Option<&T>::cloned`. -/
@[rust_fun "core::option::{core::option::Option<&'0 @T>}::cloned"]
def core.option.OptionShared0T.cloned {T : Type _} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T) :=
  fun o => match o with
    | none => ok none
    | some x => do
      let y ← cloneCloneInst.clone x
      ok (some y)

@[rust_fun "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone {T : Type _} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T) :=
  fun o => match o with
    | none => ok none
    | some x => do
      let y ← cloneCloneInst.clone x
      ok (some y)

@[rust_fun "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type _) : Result (Option T) :=
  ok none

@[rust_fun "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type _}
  (cmpPartialEqInst : core.cmp.PartialEq T T) : Option T → Option T → Result Bool :=
  fun a b => match a, b with
    | some x, some y => cmpPartialEqInst.eq x y
    | none, none => ok true
    | _, _ => ok false

/-- `Try for Option`: `branch` is `Continue(v)` on `Some(v)`, `Break(None)` on `None`. -/
@[rust_fun "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type _} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  fun o => match o with
    | some v => ok (.Continue v)
    | none => ok (.Break none)

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual (T : Type _) :
  Option Never → Result (Option T) :=
  fun _ => ok none

/-- `Debug for Option<T>` (derived): `None` writes `"None"`; `Some(x)` is
    `f.debug_tuple("Some").field(&x).finish()`, which writes `"Some("`, the field and `")"`
    (non-alternate mode; the `Formatter` model carries no flags). -/
@[rust_fun "core::option::{core::fmt::Debug<core::option::Option<@T>>}::fmt"]
def core.option.Option.Insts.CoreFmtDebug.fmt {T : Type _} (fmtDebugInst : core.fmt.Debug T) :
  Option T → core.fmt.Formatter →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun o f => match o with
    | none => core.fmt.Formatter.write_str f (toStr "None")
    | some x => do
      let (r, f) ← core.fmt.Formatter.write_str f (toStr "Some(")
      match r with
      | .Err e => ok (.Err e, f)
      | .Ok () => do
        let (r, f) ← fmtDebugInst.fmt x f
        match r with
        | .Err e => ok (.Err e, f)
        | .Ok () => core.fmt.Formatter.write_str f (toStr ")")

/-! ## `Result` -/

@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
def core.result.Result.is_err {T : Type _} {E : Type _} : core.result.Result T E → Std.Result Bool :=
  fun r => match r with
    | .Ok _ => Std.Result.ok false
    | .Err _ => Std.Result.ok true

@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T : Type _} {E : Type _} : core.result.Result T E → Std.Result (Option T) :=
  fun r => match r with
    | .Ok x => Std.Result.ok (some x)
    | .Err _ => Std.Result.ok none

/-- `unwrap_err`: panics on `Ok`. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap_err"]
def core.result.Result.unwrap_err {T : Type _} {E : Type _} (_fmtDebugInst : core.fmt.Debug T) :
  core.result.Result T E → Std.Result E :=
  fun r => match r with
    | .Ok _ => fail .panic
    | .Err e => Std.Result.ok e

@[rust_fun "core::result::{core::result::Result<@T, @E>}::and_then"]
def core.result.Result.and_then {T : Type _} {E : Type _} {U : Type _} {F : Type _}
  (opsfunctionFnOnceFTupleTResultInst : core.ops.function.FnOnce F T (core.result.Result U E)) :
  core.result.Result T E → F → Std.Result (core.result.Result U E) :=
  fun r f => match r with
    | .Ok x => opsfunctionFnOnceFTupleTResultInst.call_once f x
    | .Err e => Std.Result.ok (.Err e)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::or_else"]
def core.result.Result.or_else {T : Type _} {E : Type _} {F : Type _} {O : Type _}
  (opsfunctionFnOnceOTupleEResultInst : core.ops.function.FnOnce O E (core.result.Result T F)) :
  core.result.Result T E → O → Std.Result (core.result.Result T F) :=
  fun r op => match r with
    | .Ok x => Std.Result.ok (.Ok x)
    | .Err e => opsfunctionFnOnceOTupleEResultInst.call_once op e

@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap_or_else"]
def core.result.Result.unwrap_or_else {T : Type _} {E : Type _} {F : Type _}
  (opsfunctionFnOnceFTupleETInst : core.ops.function.FnOnce F E T) :
  core.result.Result T E → F → Std.Result T :=
  fun r f => match r with
    | .Ok x => Std.Result.ok x
    | .Err e => opsfunctionFnOnceFTupleETInst.call_once f e

/-! ## `bool` -/

@[rust_fun "core::bool::{bool}::then_some"]
def core.bool.Bool.then_some {T : Type _} : Bool → T → Result (Option T) :=
  fun b t => ok (if b then some t else none)

end Aeneas.Std
