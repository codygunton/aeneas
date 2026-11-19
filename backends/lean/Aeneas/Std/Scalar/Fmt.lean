module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public import Aeneas.Std.Scalar.Display
public import Aeneas.Std.Core.Fmt
public section

/-! # `Debug` and `LowerHex` for the integer types -/

namespace Aeneas.Std

open ScalarElab

/-! ## `LowerHex` -/

@[expose, rust_fun "core::fmt::num::{core::fmt::LowerHex<u16>}::fmt"]
def core.fmt.num.LowerHexU16.fmt (x : U16) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtLowerHex x f

@[expose, rust_fun "core::fmt::num::{core::fmt::LowerHex<u32>}::fmt"]
def U32.Insts.CoreFmtLowerHex.fmt (x : U32) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtLowerHex x f

@[expose, rust_fun "core::fmt::num::{core::fmt::LowerHex<u64>}::fmt"]
def U64.Insts.CoreFmtLowerHex.fmt (x : U64) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtLowerHex x f

@[expose, rust_fun "core::fmt::num::{core::fmt::LowerHex<i64>}::fmt"]
def I64.Insts.CoreFmtLowerHex.fmt (x : I64) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtLowerHex x f

/-! ## `Debug` (decimal, or hexadecimal for `{:x?}`/`{:X?}`) -/

uscalar @[expose, rust_fun "core::fmt::num::{core::fmt::Debug<%s>}::fmt"]
def core.fmt.num.Debug'S.fmt (x : «%S») (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  UScalar.fmtDebug x f

iscalar @[expose, rust_fun "core::fmt::num::{core::fmt::Debug<%s>}::fmt"]
def core.fmt.num.Debug'S.fmt (x : «%S») (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  IScalar.fmtDebug x f

uscalar @[expose, reducible, rust_trait_impl "core::fmt::Debug<%s>"]
def core.fmt.Debug'S : core.fmt.Debug «%S» := {
  fmt := core.fmt.num.Debug'S.fmt
}

iscalar @[expose, reducible, rust_trait_impl "core::fmt::Debug<%s>"]
def core.fmt.Debug'S : core.fmt.Debug «%S» := {
  fmt := core.fmt.num.Debug'S.fmt
}

end Aeneas.Std
