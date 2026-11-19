module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Result
public import Aeneas.Std.StringDef
public section

/-!
# Integer parsing (`FromStr`, `from_str_radix`), Rust 1.96 `from_ascii_radix`

The digits are scanned from left to right; the first error wins: `InvalidDigit` for a character
which is not a digit of the radix, `PosOverflow`/`NegOverflow` as soon as the accumulated value
leaves the range of the type (Rust checks the multiplication after the digit, so an invalid
digit is reported before the overflow it would cause).
-/

namespace Aeneas.Std

open ScalarElab Result

@[rust_type "core::num::error::IntErrorKind"]
inductive core.num.error.IntErrorKind where
  | Empty | InvalidDigit | PosOverflow | NegOverflow | Zero
deriving Inhabited, Repr, BEq, DecidableEq

@[rust_type "core::num::error::ParseIntError"]
structure core.num.error.ParseIntError where
  kind : core.num.error.IntErrorKind
deriving Inhabited, Repr, BEq, DecidableEq

/-- `char::to_digit` on an ASCII byte. -/
@[expose] def core.num.asciiDigit (b radix : Nat) : Option Nat :=
  let d :=
    if 48 ≤ b ∧ b ≤ 57 then some (b - 48)
    else if 97 ≤ b ∧ b ≤ 122 then some (b - 97 + 10)
    else if 65 ≤ b ∧ b ≤ 90 then some (b - 65 + 10)
    else none
  match d with
  | some d => if d < radix then some d else none
  | none => none

/-- `from_ascii_radix` for the integer range `[lo, hi]` (`signed`: whether `-` is accepted). -/
@[expose] def core.num.fromAsciiRadix (src : List Nat) (radix : Nat) (signed : Bool) (lo hi : Int) :
    Result (core.result.Result Int core.num.error.ParseIntError) :=
  if radix < 2 ∨ 36 < radix then fail .panic else
  let err (k : core.num.error.IntErrorKind) := ok (.Err { kind := k })
  match src with
  | [] => err .Empty
  | [43] | [45] => err .InvalidDigit
  | _ =>
    let (pos, digits) := match src with
      | 43 :: rest => (true, rest)
      | 45 :: rest => if signed then (false, rest) else (true, src)
      | _ => (true, src)
    let rec go (acc : Int) : List Nat → Result (core.result.Result Int core.num.error.ParseIntError)
      | [] => ok (.Ok acc)
      | c :: rest =>
        match core.num.asciiDigit c radix with
        | none => err .InvalidDigit
        | some d =>
          let acc := if pos then acc * radix + d else acc * radix - d
          if acc < lo then err .NegOverflow
          else if hi < acc then err .PosOverflow
          else go acc rest
    go 0 digits

@[expose] def core.num.strBytes (s : Str) : List Nat := (Slice.val (α := U8) s).map (·.val)

uscalar @[expose, rust_fun "core::num::{%s}::from_str_radix"]
def core.num.«%S».from_str_radix (s : Str) (radix : U32) :
    Result (core.result.Result «%S» core.num.error.ParseIntError) := do
  match ← core.num.fromAsciiRadix (core.num.strBytes s) radix.val false 0 (2^%BitWidth - 1 : Nat) with
  | .Ok v => ok (.Ok ⟨BitVec.ofInt _ v⟩)
  | .Err e => ok (.Err e)

iscalar @[expose, rust_fun "core::num::{%s}::from_str_radix"]
def core.num.«%S».from_str_radix (s : Str) (radix : U32) :
    Result (core.result.Result «%S» core.num.error.ParseIntError) := do
  match ← core.num.fromAsciiRadix (core.num.strBytes s) radix.val true
      (-((2^(%BitWidth - 1) : Nat) : Int)) (2^(%BitWidth - 1) - 1 : Nat) with
  | .Ok v => ok (.Ok ⟨BitVec.ofInt _ v⟩)
  | .Err e => ok (.Err e)

uscalar @[expose, rust_fun
  "core::num::{core::str::traits::FromStr<%s, core::num::error::ParseIntError>}::from_str"]
def «%S».Insts.CoreStrTraitsFromStrParseIntError.from_str (s : Str) :
    Result (core.result.Result «%S» core.num.error.ParseIntError) :=
  core.num.«%S».from_str_radix s ⟨BitVec.ofNat _ 10⟩

iscalar @[expose, rust_fun
  "core::num::{core::str::traits::FromStr<%s, core::num::error::ParseIntError>}::from_str"]
def «%S».Insts.CoreStrTraitsFromStrParseIntError.from_str (s : Str) :
    Result (core.result.Result «%S» core.num.error.ParseIntError) :=
  core.num.«%S».from_str_radix s ⟨BitVec.ofNat _ 10⟩

end Aeneas.Std
