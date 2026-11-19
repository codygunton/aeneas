/- `alloc::string` / `alloc::str`: `String` (modelled by Lean's `String`) and `str` (`Str`, the
UTF-8 bytes). Conversions from `Str` decode UTF-8: a Rust `str` is always valid UTF-8. -/
module
public import Aeneas.Std.Alloc.String
public import Aeneas.Std.Alloc.Util
public import Aeneas.Std.Alloc.SliceOps
public import Aeneas.Std.Core.Borrow
public import Aeneas.Std.Core.Hash
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.StringDef
public import Aeneas.Std.CoreStr
public section

namespace Aeneas.Std

open Result

namespace StringModel

/-- The UTF-8 bytes of a `String` as a `str`. -/
@[expose] def toStr (s : String) : Result Str :=
  AllocModel.slice (s.toUTF8.toList.map fun b => ({ bv := b.toBitVec } : U8))

/-- Decode a `str`; fails (`.panic`) on invalid UTF-8, which a Rust `str` never contains. -/
@[expose] def ofStr (s : Str) : Result String :=
  match String.fromUTF8? (ByteArray.mk (s.val.map fun b => b.bv.toNat.toUInt8).toArray) with
  | some s => ok s
  | none => fail .panic

/-- Length in bytes. -/
@[expose] def len (s : String) : Result Usize := AllocModel.usize s.utf8ByteSize

end StringModel

open StringModel

@[expose, rust_fun "alloc::string::{alloc::string::String}::new"]
def alloc.string.String.new : Result String := ok ""

@[expose, rust_fun "alloc::string::{alloc::string::String}::with_capacity"]
def alloc.string.String.with_capacity (_ : Usize) : Result String := ok ""

/-- Rust panics with "capacity overflow" past `isize::MAX` bytes. -/
@[expose, rust_fun "alloc::string::{alloc::string::String}::push_str"]
def alloc.string.String.push_str (s : String) (t : Str) : Result String := do
  let t ← ofStr t
  if s.utf8ByteSize + t.utf8ByteSize ≤ Isize.max then ok (s ++ t) else fail .panic

@[expose, rust_fun "alloc::string::{alloc::string::String}::push"]
def alloc.string.String.push (s : String) (c : Char) : Result String :=
  if s.utf8ByteSize + c.utf8Size ≤ Isize.max then ok (s.push c) else fail .panic

@[expose, rust_fun "alloc::string::{alloc::string::String}::len"]
def alloc.string.String.len (s : String) : Result Usize := StringModel.len s

@[expose, rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (s : String) : Result String := ok s

@[expose, rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq (s t : String) : Result Bool :=
  ok (s == t)

@[expose, rust_fun
  "alloc::string::{core::cmp::Eq<alloc::string::String>}::assert_fields_are_eq"]
def alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq (_ : String) : Result Unit :=
  ok ()

/-- `impl Hash for str`: `state.write_str(self)`. -/
@[expose, rust_fun "alloc::string::{core::hash::Hash<alloc::string::String>}::hash"]
def alloc.string.String.Insts.CoreHashHash.hash {H : Type _}
    (hasherInst : core.hash.Hasher H) (s : String) (state : H) : Result H := do
  let bytes ← toStr s
  hasherInst.write_str state bytes

/-- `&self[index]`: `index.index(self.as_str())`. -/
@[expose, rust_fun
  "alloc::string::{core::ops::index::Index<alloc::string::String, @I, @Clause0_Output>}::index"]
def alloc.string.String.Insts.CoreOpsIndexIndex.index {I : Type _} {Clause0_Output : Type _}
    (sliceIndexInst : core.slice.index.SliceIndex I Str Clause0_Output) (s : String) (i : I) :
    Result Clause0_Output := do
  let bytes ← toStr s
  sliceIndexInst.index i bytes

@[expose, rust_fun
  "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref (s : String) : Result Str := toStr s

@[expose, rust_fun
  "alloc::string::{core::convert::From<alloc::string::String, &'0 str>}::from"]
def alloc.string.String.Insts.CoreConvertFromShared0Str.from (s : Str) : Result String := ofStr s

@[expose, rust_fun
  "alloc::string::{core::fmt::Write<alloc::string::String>}::write_str"]
def alloc.string.String.Insts.CoreFmtWrite.write_str (s : String) (t : Str) :
    Result ((core.result.Result Unit core.fmt.Error) × String) := do
  let s ← alloc.string.String.push_str s t
  ok (.Ok (), s)

@[expose, rust_fun
  "alloc::string::{core::fmt::Write<alloc::string::String>}::write_char"]
def alloc.string.String.Insts.CoreFmtWrite.write_char (s : String) (c : Char) :
    Result ((core.result.Result Unit core.fmt.Error) × String) := do
  let s ← alloc.string.String.push s c
  ok (.Ok (), s)

@[expose, rust_fun "alloc::str::{core::borrow::Borrow<alloc::string::String, str>}::borrow"]
def alloc.string.String.Insts.CoreBorrowBorrowStr.borrow (s : String) : Result Str := toStr s

@[expose, rust_fun "alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned"]
def Str.Insts.AllocBorrowToOwnedString.to_owned (s : Str) : Result String := ofStr s

/-- `[S].join(sep)` for `S: Borrow<str>`: the borrowed pieces separated by `sep`. -/
@[expose, rust_fun
  "alloc::str::{alloc::slice::Join<[@S], &'0 str, alloc::string::String>}::join"]
def Slice.Insts.AllocSliceJoinShared0StrString.join {S : Type _}
    (borrowInst : core.borrow.Borrow S Str) (s : Slice S) (sep : Str) : Result String := do
  let pieces ← s.val.mapM borrowInst.borrow
  let bytes := (pieces.map Slice.val).intersperse sep.val |>.flatten
  let bytes ← AllocModel.slice bytes
  ofStr bytes

/-- `str::replace`: copies the haystack, substituting `to'` for every non-overlapping match of
    the pattern, leftmost first (`match_indices`). -/
@[expose, rust_fun "alloc::str::{str}::replace"]
def alloc.str.Str.replace {P : Type _} (patternInst : core.str.pattern.Pattern P) (s : Str)
    (pat : P) (to' : Str) : Result String := do
  let found := core.str.pattern.Pattern.matchIndices patternInst s pat
  let (out, lastEnd) := found.foldl (fun (acc : List U8 × Nat) (m : Nat × Nat) =>
    let (out, lastEnd) := acc
    (out ++ (s.val.drop lastEnd).take (m.1 - lastEnd) ++ to'.val, m.1 + m.2)) ([], 0)
  let bytes ← AllocModel.slice (out ++ s.val.drop lastEnd)
  ofStr bytes

end Aeneas.Std
