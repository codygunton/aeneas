module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public import Aeneas.Std.Core.Fmt
public section

/-! # `Display`, `LowerHex` and `UpperHex` for the integer types (`Formatter::pad_integral`) -/

namespace Aeneas.Std

open ScalarElab

/-- `Display` of an integer given by its sign and magnitude. -/
@[expose] def core.fmt.num.fmtDecimal (isNonnegative : Bool) (mag : Nat) (f : core.fmt.Formatter) :
    core.fmt.FmtResult :=
  f.pad_integral isNonnegative "" (toString mag)

/-- `LowerHex`/`UpperHex` of the bits of an integer (Rust prints the two's complement of
    negative numbers). -/
@[expose] def core.fmt.num.fmtHex (upper : Bool) (bits : Nat) (f : core.fmt.Formatter) :
    core.fmt.FmtResult :=
  let digits := String.ofList (Nat.toDigits 16 bits)
  f.pad_integral true "0x" (if upper then digits.toUpper else digits)

/-- `Debug` of an integer: hexadecimal for `{:x?}`/`{:X?}`, decimal otherwise. -/
@[expose] def core.fmt.num.fmtDebugInt (isNonnegative : Bool) (mag bits : Nat)
    (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  if f.debugLowerHex then core.fmt.num.fmtHex false bits f
  else if f.debugUpperHex then core.fmt.num.fmtHex true bits f
  else core.fmt.num.fmtDecimal isNonnegative mag f

@[expose] def UScalar.fmtDisplay {ty} (x : UScalar ty) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  core.fmt.num.fmtDecimal true x.val f
@[expose] def IScalar.fmtDisplay {ty} (x : IScalar ty) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  core.fmt.num.fmtDecimal (0 ≤ x.val) x.val.natAbs f
@[expose] def UScalar.fmtLowerHex {ty} (x : UScalar ty) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  core.fmt.num.fmtHex false x.bv.toNat f
@[expose] def IScalar.fmtLowerHex {ty} (x : IScalar ty) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  core.fmt.num.fmtHex false x.bv.toNat f
@[expose] def UScalar.fmtDebug {ty} (x : UScalar ty) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  core.fmt.num.fmtDebugInt true x.val x.bv.toNat f
@[expose] def IScalar.fmtDebug {ty} (x : IScalar ty) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  core.fmt.num.fmtDebugInt (0 ≤ x.val) x.val.natAbs x.bv.toNat f

/-! The `core::fmt::num::imp` impls (all the integer types but `u128`/`i128`). -/

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u8>}::fmt"]
def core.fmt.num.imp.DisplayU8.fmt (x : U8) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u16>}::fmt"]
def core.fmt.num.imp.DisplayU16.fmt (x : U16) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u32>}::fmt"]
def core.fmt.num.imp.DisplayU32.fmt (x : U32) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u64>}::fmt"]
def core.fmt.num.imp.DisplayU64.fmt (x : U64) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<usize>}::fmt"]
def core.fmt.num.imp.DisplayUsize.fmt (x : Usize) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i8>}::fmt"]
def core.fmt.num.imp.DisplayI8.fmt (x : I8) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i16>}::fmt"]
def core.fmt.num.imp.DisplayI16.fmt (x : I16) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i32>}::fmt"]
def core.fmt.num.imp.DisplayI32.fmt (x : I32) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i64>}::fmt"]
def core.fmt.num.imp.DisplayI64.fmt (x : I64) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<isize>}::fmt"]
def core.fmt.num.imp.DisplayIsize.fmt (x : Isize) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtDisplay x f

/-! `u128`/`i128` are formatted outside of `imp` since Rust 1.9x. -/

@[expose, rust_fun "core::fmt::num::{core::fmt::Display<u128>}::fmt"]
def U128.Insts.CoreFmtDisplay.fmt (x : U128) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtDisplay x f
@[expose, rust_fun "core::fmt::num::{core::fmt::Display<i128>}::fmt"]
def I128.Insts.CoreFmtDisplay.fmt (x : I128) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtDisplay x f
end Aeneas.Std
