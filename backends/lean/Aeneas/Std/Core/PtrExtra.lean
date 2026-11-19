module
public import Aeneas.Std.RawPtr
public section

@[expose] section

/-! `core::ptr::NonNull` / `core::ptr::Unique`, over the value-based raw pointer model
(`RawPtr` carries the pointee). -/

namespace Aeneas.Std

/-- `NonNull<T> { pointer: *const T }`. -/
@[rust_type "core::ptr::non_null::NonNull" (body := .opaque)]
structure core.ptr.non_null.NonNull (T : Type u) where
  pointer : ConstRawPtr T

/-- `Unique<T> { pointer: NonNull<T>, _marker: PhantomData<T> }`. -/
@[rust_type "core::ptr::unique::Unique" (body := .opaque)]
structure core.ptr.unique.Unique (T : Type u) where
  pointer : core.ptr.non_null.NonNull T

end Aeneas.Std
