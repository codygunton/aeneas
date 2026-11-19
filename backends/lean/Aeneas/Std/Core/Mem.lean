module
public import Aeneas.Std.Primitives
public import Aeneas.Std.Core.Default
public section

@[expose] section

namespace Aeneas.Std

open Result

/-! `core::mem` types and functions. -/

/-- `core::mem::maybe_uninit::MaybeUninit<T>`: `none` is uninitialized memory. Reading an
    uninitialized value (`assume_init` on `none`) is undefined behaviour in Rust; models
    fail with `.panic` there. -/
@[rust_type "core::mem::maybe_uninit::MaybeUninit"]
structure core.mem.maybe_uninit.MaybeUninit (T : Type u) where
  value : Option T

/-- `core::mem::manually_drop::ManuallyDrop<T>`: dropping is not modelled, so this is a
    plain wrapper. -/
@[rust_type "core::mem::manually_drop::ManuallyDrop"]
structure core.mem.manually_drop.ManuallyDrop (T : Type u) where
  value : T

/-- `core::mem::take`: returns the old value and leaves `T::default()` in its place.
    Output: (old value, new value of the place). -/
@[rust_fun "core::mem::take"]
def core.mem.take {T : Type _} (defaultDefaultInst : core.default.Default T) (dest : T) :
    Result (T × T) := do
  let d ← defaultDefaultInst.default
  ok (dest, d)

end Aeneas.Std
