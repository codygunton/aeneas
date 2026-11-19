/- `alloc::borrow`: `ToOwned` and `Cow`. -/
module
public import Aeneas.Std.Core.Borrow
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

open Result

@[rust_trait "alloc::borrow::ToOwned" (parentClauses := ["coreborrowBorrowInst"])]
structure alloc.borrow.ToOwned (Self : Type _) (Self_Owned : Type _) where
  coreborrowBorrowInst : core.borrow.Borrow Self_Owned Self
  to_owned : Self → Result Self_Owned

@[rust_type "alloc::borrow::Cow"]
inductive alloc.borrow.Cow (B : Type u) (Clause0_Owned : Type v) where
| Borrowed : B → alloc.borrow.Cow B Clause0_Owned
| Owned : Clause0_Owned → alloc.borrow.Cow B Clause0_Owned

/-- Formats the borrowed or owned value with its own `Display`. -/
@[expose, rust_fun
  "alloc::borrow::{core::fmt::Display<alloc::borrow::Cow<'0, @B, @Clause1_Owned>>}::fmt"]
def alloc.borrow.Cow.Insts.CoreFmtDisplay.fmt {B : Type _} {Clause1_Owned : Type _}
    (displayB : core.fmt.Display B) (_toOwnedInst : alloc.borrow.ToOwned B Clause1_Owned)
    (displayOwned : core.fmt.Display Clause1_Owned) (c : alloc.borrow.Cow B Clause1_Owned)
    (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  match c with
  | .Borrowed b => displayB.fmt b f
  | .Owned o => displayOwned.fmt o f

end Aeneas.Std
