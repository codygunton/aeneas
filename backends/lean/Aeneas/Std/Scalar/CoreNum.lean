module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public import Aeneas.Std.Scalar.CloneCopy
public import Aeneas.Std.Core.Core
public section

/-!
# Integer methods of `core::num` (Rust 1.96 semantics)

Executable models of the inherent methods of the integer types (`wrapping_div`,
`checked_shl`, `trailing_zeros`, ...), of `core::num::nonzero::NonZero` and of the
`core::num::niche_types` wrappers. Panics are `fail`s (`divisionByZero` for divisions by zero, as
for `/`; `integerOverflow` where the debug build panics on overflow; `panic` otherwise).
-/

namespace Aeneas.Std

open ScalarElab Result

/-! ## Bit counting on naturals -/

/-- Number of trailing zero bits of `n` seen as a `bits`-bit number. -/
@[expose] def Nat.trailingZerosN (bits n : Nat) : Nat :=
  let rec go (fuel n acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 => if n % 2 == 1 then acc else go fuel (n / 2) (acc + 1)
  go bits n 0

/-- Number of leading zero bits of `n < 2^bits`. -/
@[expose] def Nat.leadingZerosN (bits n : Nat) : Nat :=
  if n == 0 then bits else bits - (Nat.log2 n + 1)

/-- Number of one bits of `n`. -/
@[expose] def Nat.countOnesN (bits n : Nat) : Nat :=
  let rec go (fuel n acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 => go fuel (n / 2) (acc + n % 2)
  go bits n 0

@[expose] def UScalar.mkU32 (n : Nat) : U32 := ⟨BitVec.ofNat _ n⟩

/-! ## Unsigned integers -/

uscalar @[expose, rust_fun "core::num::{%s}::wrapping_div"]
def core.num.«%S».wrapping_div (x y : «%S») : Result «%S» :=
  if y.val = 0 then fail .divisionByZero else ok ⟨BitVec.udiv x.bv y.bv⟩

uscalar @[expose, rust_fun "core::num::{%s}::wrapping_neg"]
def core.num.«%S».wrapping_neg (x : «%S») : Result «%S» := ok ⟨-x.bv⟩

uscalar @[expose, rust_fun "core::num::{%s}::checked_shl"]
def core.num.«%S».checked_shl (x : «%S») (rhs : U32) : Result (Option «%S») :=
  ok (if rhs.val < %BitWidth then some ⟨x.bv <<< rhs.val⟩ else none)

uscalar @[expose, rust_fun "core::num::{%s}::checked_shr"]
def core.num.«%S».checked_shr (x : «%S») (rhs : U32) : Result (Option «%S») :=
  ok (if rhs.val < %BitWidth then some ⟨x.bv >>> rhs.val⟩ else none)

uscalar @[expose, rust_fun "core::num::{%s}::checked_ilog2"]
def core.num.«%S».checked_ilog2 (x : «%S») : Result (Option U32) :=
  ok (if x.val = 0 then none else some (UScalar.mkU32 (Nat.log2 x.val)))

-- Panics on `0` ("argument of integer logarithm must be positive").
uscalar @[expose, rust_fun "core::num::{%s}::ilog2"]
def core.num.«%S».ilog2 (x : «%S») : Result U32 :=
  if x.val = 0 then fail .panic else ok (UScalar.mkU32 (Nat.log2 x.val))

uscalar @[expose, rust_fun "core::num::{%s}::trailing_zeros"]
def core.num.«%S».trailing_zeros (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.trailingZerosN %BitWidth x.val))

uscalar @[expose, rust_fun "core::num::{%s}::trailing_ones"]
def core.num.«%S».trailing_ones (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.trailingZerosN %BitWidth (~~~x.bv).toNat))

uscalar @[expose, rust_fun "core::num::{%s}::leading_ones"]
def core.num.«%S».leading_ones (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.leadingZerosN %BitWidth (~~~x.bv).toNat))

uscalar @[expose, rust_fun "core::num::{%s}::count_ones"]
def core.num.«%S».count_ones (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.countOnesN %BitWidth x.val))

uscalar @[expose, rust_fun "core::num::{%s}::saturating_mul"]
def core.num.«%S».saturating_mul (x y : «%S») : Result «%S» :=
  ok ⟨BitVec.ofNat _ (min (x.val * y.val) (2^%BitWidth - 1))⟩

/-! ## Signed integers -/

iscalar @[expose, rust_fun "core::num::{%s}::wrapping_div"]
def core.num.«%S».wrapping_div (x y : «%S») : Result «%S» :=
  if y.val = 0 then fail .divisionByZero else ok ⟨BitVec.sdiv x.bv y.bv⟩

iscalar @[expose, rust_fun "core::num::{%s}::wrapping_neg"]
def core.num.«%S».wrapping_neg (x : «%S») : Result «%S» := ok ⟨-x.bv⟩

iscalar @[expose, rust_fun "core::num::{%s}::checked_neg"]
def core.num.«%S».checked_neg (x : «%S») : Result (Option «%S») :=
  ok (if x.val = -(2^(%BitWidth - 1) : Nat) then none else some ⟨-x.bv⟩)

-- `abs` panics on `MIN` in debug builds ("attempt to negate with overflow").
iscalar @[expose, rust_fun "core::num::{%s}::abs"]
def core.num.«%S».abs (x : «%S») : Result «%S» :=
  if x.val = -(2^(%BitWidth - 1) : Nat) then fail .integerOverflow
  else if x.val < 0 then ok ⟨-x.bv⟩ else ok x

iscalar @[expose, rust_fun "core::num::{%s}::checked_shl"]
def core.num.«%S».checked_shl (x : «%S») (rhs : U32) : Result (Option «%S») :=
  ok (if rhs.val < %BitWidth then some ⟨x.bv <<< rhs.val⟩ else none)

-- Arithmetic shift.
iscalar @[expose, rust_fun "core::num::{%s}::checked_shr"]
def core.num.«%S».checked_shr (x : «%S») (rhs : U32) : Result (Option «%S») :=
  ok (if rhs.val < %BitWidth then some ⟨x.bv.sshiftRight rhs.val⟩ else none)

iscalar @[expose, rust_fun "core::num::{%s}::checked_ilog2"]
def core.num.«%S».checked_ilog2 (x : «%S») : Result (Option U32) :=
  ok (if x.val ≤ 0 then none else some (UScalar.mkU32 (Nat.log2 x.val.toNat)))

iscalar @[expose, rust_fun "core::num::{%s}::ilog2"]
def core.num.«%S».ilog2 (x : «%S») : Result U32 :=
  if x.val ≤ 0 then fail .panic else ok (UScalar.mkU32 (Nat.log2 x.val.toNat))

iscalar @[expose, rust_fun "core::num::{%s}::trailing_zeros"]
def core.num.«%S».trailing_zeros (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.trailingZerosN %BitWidth x.bv.toNat))

iscalar @[expose, rust_fun "core::num::{%s}::trailing_ones"]
def core.num.«%S».trailing_ones (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.trailingZerosN %BitWidth (~~~x.bv).toNat))

iscalar @[expose, rust_fun "core::num::{%s}::leading_ones"]
def core.num.«%S».leading_ones (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.leadingZerosN %BitWidth (~~~x.bv).toNat))

iscalar @[expose, rust_fun "core::num::{%s}::count_ones"]
def core.num.«%S».count_ones (x : «%S») : Result U32 :=
  ok (UScalar.mkU32 (Nat.countOnesN %BitWidth x.bv.toNat))

/-! ## `usize::MIN`/`MAX` of the legacy `core::usize` module -/

@[expose, rust_const "core::legacy_int_modules::usize::MAX" (canFail := true)]
def core.legacy_int_modules.usize.MAX : Result Usize := ok core.num.Usize.MAX

@[expose, rust_const "core::legacy_int_modules::usize::MIN" (canFail := true)]
def core.legacy_int_modules.usize.MIN : Result Usize := ok ⟨0⟩

/-! ## Niche types and `NonZero` -/

/-- The niche wrappers of `core::num::niche_types` are the underlying integers. -/
@[expose, reducible, rust_type "core::num::niche_types::NonZeroU8Inner"]
def core.num.niche_types.NonZeroU8Inner : Type := U8
@[expose, reducible, rust_type "core::num::niche_types::NonZeroU64Inner"]
def core.num.niche_types.NonZeroU64Inner : Type := U64
@[expose, reducible, rust_type "core::num::niche_types::UsizeNoHighBit"]
def core.num.niche_types.UsizeNoHighBit : Type := Usize

@[expose, rust_fun
  "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU8Inner>}::clone"]
def core.num.niche_types.NonZeroU8Inner.Insts.CoreCloneClone.clone
  (x : core.num.niche_types.NonZeroU8Inner) : Result core.num.niche_types.NonZeroU8Inner := ok x

@[expose, rust_fun
  "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU64Inner>}::clone"]
def core.num.niche_types.NonZeroU64Inner.Insts.CoreCloneClone.clone
  (x : core.num.niche_types.NonZeroU64Inner) : Result core.num.niche_types.NonZeroU64Inner := ok x

/-- `ZeroablePrimitive`: the integer types which have a `NonZero` version. Besides the `Copy`
    parent clauses of the Rust trait, the model carries the zero test (Rust's `NonZero::new`
    relies on the niche of `NonZeroInner`). -/
@[rust_trait "core::num::nonzero::ZeroablePrimitive"
  (parentClauses := ["markerCopyInst", "markerCopyInst1"])]
structure core.num.nonzero.ZeroablePrimitive (Self : Type _) (Self_NonZeroInner : Type _) where
  markerCopyInst : core.marker.Copy Self
  markerCopyInst1 : core.marker.Copy Self_NonZeroInner
  isZero : Self → Bool

@[expose, reducible, rust_trait_impl
  "core::num::nonzero::ZeroablePrimitive<u8, core::num::niche_types::NonZeroU8Inner>"]
def core.num.nonzero.ZeroablePrimitiveU8 :
  core.num.nonzero.ZeroablePrimitive U8 core.num.niche_types.NonZeroU8Inner := {
  markerCopyInst := core.marker.CopyU8
  markerCopyInst1 := core.marker.CopyU8
  isZero := fun x => x.val == 0 }

@[expose, reducible, rust_trait_impl
  "core::num::nonzero::ZeroablePrimitive<u64, core::num::niche_types::NonZeroU64Inner>"]
def core.num.nonzero.ZeroablePrimitiveU64 :
  core.num.nonzero.ZeroablePrimitive U64 core.num.niche_types.NonZeroU64Inner := {
  markerCopyInst := core.marker.CopyU64
  markerCopyInst1 := core.marker.CopyU64
  isZero := fun x => x.val == 0 }

/-- `NonZero<T>` is a (non-zero) `T`. -/
@[expose, reducible, rust_type "core::num::nonzero::NonZero"]
def core.num.nonzero.NonZero.{u, v} (T : Type u) (_Clause0_NonZeroInner : Type v) : Type u := T

@[expose, rust_fun
  "core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::new"]
def core.num.nonzero.NonZero.new {T : Type _} {Clause0_NonZeroInner : Type _}
  (ZeroablePrimitiveInst : core.num.nonzero.ZeroablePrimitive T Clause0_NonZeroInner) (x : T) :
  Result (Option (core.num.nonzero.NonZero T Clause0_NonZeroInner)) :=
  ok (if ZeroablePrimitiveInst.isZero x then none else some x)

@[expose, rust_fun
  "core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::get"]
def core.num.nonzero.NonZero.get {T : Type _} {Clause0_NonZeroInner : Type _}
  (_ : core.num.nonzero.ZeroablePrimitive T Clause0_NonZeroInner)
  (x : core.num.nonzero.NonZero T Clause0_NonZeroInner) : Result T := ok x

@[expose, rust_fun
  "core::num::nonzero::{core::num::nonzero::NonZero<u64, core::num::niche_types::NonZeroU64Inner>}::trailing_zeros"]
def core.num.nonzero.NonZeroU64NonZeroU64Inner.trailing_zeros
  (x : core.num.nonzero.NonZero U64 core.num.niche_types.NonZeroU64Inner) : Result U32 :=
  core.num.U64.trailing_zeros x

end Aeneas.Std
