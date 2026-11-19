module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Core.Cmp
public section

/-!
# Rust `f32` / `f64`

`F32`/`F64` are Lean's `Float32`/`Float`, which compile to C `float`/`double`: arithmetic
(`+ - * /`, negation, comparisons, `f32 <-> f64` casts) is performed by the hardware, exactly
like the native Rust code. Everything whose result is not given by a single IEEE operation
(`%`, casts from/to integers, which Rust defines precisely, including saturation) is
implemented on the bit representation, so the result is bit-exact and does not depend on C
undefined behaviour.

Aeneas extracts float literals as `F32.ofBitsNat <bits>`, float binary operations as
`F32.add`, `F32.lt`, ..., negation as `F32.neg` and casts as `F32.toUScalar`, `UScalar.toF32`,
`F32.toF64`, ...
-/

namespace Aeneas.Std

/-- An `f32`, stored as its IEEE bits (so that copies, `to_bits`/`from_bits` and NaN payloads
    are exact whatever the evaluator); operations go through `Float32`. -/
structure F32 where
  bits : UInt32
deriving Inhabited, BEq

/-- An `f64`, stored as its IEEE bits; operations go through `Float`. -/
structure F64 where
  bits : UInt64
deriving Inhabited, BEq

@[inline] def F32.hw (x : F32) : Float32 := Float32.ofBits x.bits
@[inline] def F32.ofHw (f : Float32) : F32 := ⟨f.toBits⟩
@[inline] def F64.hw (x : F64) : Float := Float.ofBits x.bits
@[inline] def F64.ofHw (f : Float) : F64 := ⟨f.toBits⟩

/-! ## Bit-level encoding -/

/-- An IEEE binary format: `mantBits` stored fraction bits, `expBits` exponent bits. -/
structure FloatFmt where
  mantBits : Nat
  expBits : Nat

def FloatFmt.binary32 : FloatFmt := ⟨23, 8⟩
def FloatFmt.binary64 : FloatFmt := ⟨52, 11⟩

def FloatFmt.bias (f : FloatFmt) : Nat := 2^(f.expBits - 1) - 1
def FloatFmt.signBit (f : FloatFmt) : Nat := 2^(f.mantBits + f.expBits)
def FloatFmt.infBits (f : FloatFmt) : Nat := (2^f.expBits - 1) * 2^f.mantBits

/-- A decoded float: `finite neg m e` stands for `(-1)^neg * m * 2^e`. -/
inductive FloatVal where
  | nan
  | inf (neg : Bool)
  | finite (neg : Bool) (m : Nat) (e : Int)

def FloatFmt.decode (f : FloatFmt) (bits : Nat) : FloatVal :=
  let neg := (bits / f.signBit) % 2 == 1
  let exp := (bits / 2^f.mantBits) % 2^f.expBits
  let frac := bits % 2^f.mantBits
  if exp == 2^f.expBits - 1 then
    if frac == 0 then .inf neg else .nan
  else if exp == 0 then .finite neg frac (1 - (f.bias : Int) - f.mantBits)
  else .finite neg (frac + 2^f.mantBits) ((exp : Int) - f.bias - f.mantBits)

/-- `m / 2^s` rounded to nearest, ties to even (`s ≥ 1`). -/
def roundShiftRight (m s : Nat) : Nat :=
  let q := m / 2^s
  let r := m % 2^s
  let half := 2^(s - 1)
  if r > half || (r == half && q % 2 == 1) then q + 1 else q

/-- The bits of the float nearest (ties to even) to `(-1)^neg * m * 2^e`. -/
def FloatFmt.encode (f : FloatFmt) (neg : Bool) (m : Nat) (e : Int) : Nat :=
  let sign := if neg then f.signBit else 0
  if m == 0 then sign else
  let p : Int := Nat.log2 m + 1
  let bigE := e + p - 1
  let emin : Int := 1 - (f.bias : Int)
  let q := max (bigE - f.mantBits) (emin - f.mantBits)
  let shift := e - q
  let r := if shift ≥ 0 then m * 2^shift.toNat else roundShiftRight m (-shift).toNat
  let (r, q) := if r == 2^(f.mantBits + 1) then (r / 2, q + 1) else (r, q)
  if r < 2^f.mantBits then sign + r
  else
    let be := q + f.mantBits + f.bias
    if be ≥ 2^f.expBits - 1 then sign + f.infBits
    else sign + be.toNat * 2^f.mantBits + (r - 2^f.mantBits)

/-- Truncation toward zero of a decoded finite value. -/
def FloatVal.truncInt (neg : Bool) (m : Nat) (e : Int) : Int :=
  let mag : Nat := if e ≥ 0 then m * 2^e.toNat else m / 2^(-e).toNat
  if neg then -(mag : Int) else mag

/-- Rust `as` from a float to an integer in `[lo, hi]`: truncate, saturate, `NaN ↦ 0`. -/
def FloatFmt.toIntSat (f : FloatFmt) (bits : Nat) (lo hi : Int) : Int :=
  match f.decode bits with
  | .nan => 0
  | .inf neg => if neg then lo else hi
  | .finite neg m e => max lo (min hi (FloatVal.truncInt neg m e))

/-! ## `f32` -/

def F32.ofBitsNat (n : Nat) : F32 := ⟨UInt32.ofNat n⟩
def F32.bitsNat (x : F32) : Nat := x.bits.toNat

@[inline] def F32.add (x y : F32) : F32 := F32.ofHw (Float32.add x.hw y.hw)
@[inline] def F32.sub (x y : F32) : F32 := F32.ofHw (Float32.sub x.hw y.hw)
@[inline] def F32.mul (x y : F32) : F32 := F32.ofHw (Float32.mul x.hw y.hw)
@[inline] def F32.div (x y : F32) : F32 := F32.ofHw (Float32.div x.hw y.hw)
/-- Negation flips the sign bit (exact, also on NaNs, as on x86-64/AArch64). -/
@[inline] def F32.neg (x : F32) : F32 := ⟨x.bits ^^^ 0x80000000⟩

@[inline] def F32.eq (x y : F32) : Bool := Float32.beq x.hw y.hw
@[inline] def F32.ne (x y : F32) : Bool := !Float32.beq x.hw y.hw
@[inline] def F32.lt (x y : F32) : Bool := Float32.lt x.hw y.hw
@[inline] def F32.le (x y : F32) : Bool := Float32.le x.hw y.hw
@[inline] def F32.gt (x y : F32) : Bool := Float32.lt y.hw x.hw
@[inline] def F32.ge (x y : F32) : Bool := Float32.le y.hw x.hw

/-- Exact `fmod` on decoded values: `x - trunc(x / y) * y`, with the sign of `x`.
    `none` for the invalid cases (`NaN` operand, `x` infinite, `y` zero). -/
def FloatFmt.fmod (f : FloatFmt) (x y : Nat) : Option Nat :=
  match f.decode x, f.decode y with
  | .finite xn xm xe, .inf _ => some (f.encode xn xm xe)
  | .finite xn xm xe, .finite _ ym ye =>
    if ym == 0 then none
    else if xm == 0 then some (f.encode xn 0 0)
    else
      let e := min xe ye
      let xx := xm * 2^(xe - e).toNat
      let yy := ym * 2^(ye - e).toNat
      some (f.encode xn (xx % yy) e)
  | _, _ => none

/-- Rust `%` on `f32` (C `fmodf`). Invalid cases produce the NaN of `(x * y) / (x * y)`, as glibc. -/
def F32.rem (x y : F32) : F32 :=
  match FloatFmt.binary32.fmod x.bitsNat y.bitsNat with
  | some b => F32.ofBitsNat b
  | none => let p := Float32.mul x.hw y.hw; F32.ofHw (Float32.div p p)

/-! ## `f64` -/

def F64.ofBitsNat (n : Nat) : F64 := ⟨UInt64.ofNat n⟩
def F64.bitsNat (x : F64) : Nat := x.bits.toNat

@[inline] def F64.add (x y : F64) : F64 := F64.ofHw (Float.add x.hw y.hw)
@[inline] def F64.sub (x y : F64) : F64 := F64.ofHw (Float.sub x.hw y.hw)
@[inline] def F64.mul (x y : F64) : F64 := F64.ofHw (Float.mul x.hw y.hw)
@[inline] def F64.div (x y : F64) : F64 := F64.ofHw (Float.div x.hw y.hw)
@[inline] def F64.neg (x : F64) : F64 := ⟨x.bits ^^^ 0x8000000000000000⟩

@[inline] def F64.eq (x y : F64) : Bool := Float.beq x.hw y.hw
@[inline] def F64.ne (x y : F64) : Bool := !Float.beq x.hw y.hw
@[inline] def F64.lt (x y : F64) : Bool := Float.lt x.hw y.hw
@[inline] def F64.le (x y : F64) : Bool := Float.le x.hw y.hw
@[inline] def F64.gt (x y : F64) : Bool := Float.lt y.hw x.hw
@[inline] def F64.ge (x y : F64) : Bool := Float.le y.hw x.hw

/-- Rust `%` on `f64` (C `fmod`). -/
def F64.rem (x y : F64) : F64 :=
  match FloatFmt.binary64.fmod x.bitsNat y.bitsNat with
  | some b => F64.ofBitsNat b
  | none => let p := Float.mul x.hw y.hw; F64.ofHw (Float.div p p)

/-! ## Casts (Rust `as`) -/

/-- `f32 as f64` (exact; NaN payloads are kept and quieted by the hardware, as natively). -/
@[inline] def F32.toF64 (x : F32) : F64 := F64.ofHw (Float32.toFloat x.hw)
/-- `f64 as f32` (round to nearest even, by the hardware). -/
@[inline] def F64.toF32 (x : F64) : F32 := F32.ofHw (Float.toFloat32 x.hw)

def IScalarTy.minInt (ty : IScalarTy) : Int := -(2^(ty.numBits - 1) : Nat)
def IScalarTy.maxInt (ty : IScalarTy) : Int := (2^(ty.numBits - 1) - 1 : Nat)

def F32.toUScalar (ty : UScalarTy) (x : F32) : UScalar ty :=
  ⟨BitVec.ofInt _ (FloatFmt.binary32.toIntSat x.bitsNat 0 (2^ty.numBits - 1 : Nat))⟩
def F32.toIScalar (ty : IScalarTy) (x : F32) : IScalar ty :=
  ⟨BitVec.ofInt _ (FloatFmt.binary32.toIntSat x.bitsNat ty.minInt ty.maxInt)⟩
def F64.toUScalar (ty : UScalarTy) (x : F64) : UScalar ty :=
  ⟨BitVec.ofInt _ (FloatFmt.binary64.toIntSat x.bitsNat 0 (2^ty.numBits - 1 : Nat))⟩
def F64.toIScalar (ty : IScalarTy) (x : F64) : IScalar ty :=
  ⟨BitVec.ofInt _ (FloatFmt.binary64.toIntSat x.bitsNat ty.minInt ty.maxInt)⟩

/-- Integer to float, round to nearest even (Rust `as`). -/
def F32.ofInt (i : Int) : F32 := F32.ofBitsNat (FloatFmt.binary32.encode (i < 0) i.natAbs 0)
def F64.ofInt (i : Int) : F64 := F64.ofBitsNat (FloatFmt.binary64.encode (i < 0) i.natAbs 0)

def UScalar.toF32 {ty : UScalarTy} (x : UScalar ty) : F32 := F32.ofInt x.val
def IScalar.toF32 {ty : IScalarTy} (x : IScalar ty) : F32 := F32.ofInt x.val
def UScalar.toF64 {ty : UScalarTy} (x : UScalar ty) : F64 := F64.ofInt x.val
def IScalar.toF64 {ty : IScalarTy} (x : IScalar ty) : F64 := F64.ofInt x.val

/-! ## Library functions -/

@[rust_fun "core::f32::{f32}::to_bits"]
def core.f32.F32.to_bits (x : F32) : Result U32 := .ok ⟨BitVec.ofNat _ x.bitsNat⟩

@[rust_fun "core::f32::{f32}::from_bits"]
def core.f32.F32.from_bits (x : U32) : Result F32 := .ok (F32.ofBitsNat x.val)

@[rust_fun "core::f64::{f64}::to_bits"]
def core.f64.F64.to_bits (x : F64) : Result U64 := .ok ⟨BitVec.ofNat _ x.bitsNat⟩

@[rust_fun "core::f64::{f64}::from_bits"]
def core.f64.F64.from_bits (x : U64) : Result F64 := .ok (F64.ofBitsNat x.val)

/-- IEEE partial order: `None` iff one operand is NaN. -/
def F32.partialCmp (x y : F32) : Option Ordering :=
  if F32.lt x y then some .lt
  else if F32.gt x y then some .gt
  else if F32.eq x y then some .eq
  else none

def F64.partialCmp (x y : F64) : Option Ordering :=
  if F64.lt x y then some .lt
  else if F64.gt x y then some .gt
  else if F64.eq x y then some .eq
  else none

@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<f32, f32>}::partial_cmp"]
def F32.Insts.CoreCmpPartialOrdF32.partial_cmp (x y : F32) : Result (Option Ordering) :=
  .ok (F32.partialCmp x y)

@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<f64, f64>}::partial_cmp"]
def F64.Insts.CoreCmpPartialOrdF64.partial_cmp (x y : F64) : Result (Option Ordering) :=
  .ok (F64.partialCmp x y)

@[rust_fun "core::default::{core::default::Default<f64>}::default"]
def F64.Insts.CoreDefaultDefault.default : Result F64 := .ok (F64.ofBitsNat 0)

end Aeneas.Std
