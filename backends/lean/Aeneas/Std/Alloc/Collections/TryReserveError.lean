/- `alloc::collections::TryReserveError`. -/
module
public import Aeneas.Std.Primitives
public meta import Aeneas.Extract.Extract
public section

namespace Aeneas.Std

/-- The error kind of a failed reservation (`TryReserveErrorKind`). Allocation failure is not
    modelled, so only `CapacityOverflow` is ever produced. -/
@[rust_type "alloc::collections::TryReserveError" (body := .opaque)]
inductive alloc.collections.TryReserveError where
  | CapacityOverflow
  | AllocError

end Aeneas.Std
