module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.Core.Default
public import Aeneas.Std.Core.Hash
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Borrow
public import Aeneas.Std.Array.ArraySlice
public import Aeneas.Std.Scalar.Bitwise
public import Aeneas.Std.Scalar.OverflowingOps.Add
public section

@[expose] section

/-! Small `core` items: `any`, `hint`, `intrinsics`, `panicking`, `default`, `marker`,
`mem::size_of`, scalar operator impls, `[T; N]` borrow/hash/eq (Rust 1.96, 64-bit target). -/

namespace Aeneas.Std

open Result

/-! ## `core::any` -/

/-- `core::any::TypeId`: an opaque 128-bit type hash. -/
@[rust_type "core::any::TypeId" (body := .opaque)]
structure core.any.TypeId where
  t : U64 × U64

/-- `<T as Any>::type_id`. Lean types are erased at runtime, so the hash of the Rust type cannot
    be computed: the model fails with `.undef`. -/
@[rust_fun "core::any::{core::any::Any<@T>}::type_id"]
def core.any.Any.Blanket.type_id {T : Type _} : T → Result core.any.TypeId :=
  fun _ => fail .undef

/-! ## `core::hint`, `core::intrinsics`, `core::panicking` -/

@[rust_fun "core::hint::must_use"]
def core.hint.must_use {T : Type _} : T → Result T :=
  fun x => ok x

/-- Integer types with a wrapping addition and overflow flag (`add_with_overflow`). -/
class core.intrinsics.AddWithOverflow (T : Type u) where
  addWithOverflow : T → T → Result (T × Bool)

instance {ty} : core.intrinsics.AddWithOverflow (UScalar ty) where
  addWithOverflow x y := ok (UScalar.overflowing_add x y)

instance {ty} : core.intrinsics.AddWithOverflow (IScalar ty) where
  addWithOverflow x y := ok (IScalar.overflowing_add x y)

/-- `core::intrinsics::add_with_overflow`: only defined for the integer types; the
    instance argument selects the integer type (synthesized at the call site). -/
@[rust_fun "core::intrinsics::add_with_overflow"]
def core.intrinsics.add_with_overflow {T : Type _} (_markerCopyInst : core.marker.Copy T)
  [inst : core.intrinsics.AddWithOverflow T] : T → T → Result (T × Bool) :=
  inst.addWithOverflow

/-- `panic_const_add_overflow`: "attempt to add with overflow". -/
@[rust_fun "core::panicking::panic_const::panic_const_add_overflow"]
def core.panicking.panic_const.panic_const_add_overflow : Result Never :=
  fail .integerOverflow

/-- `panic_const_shl_overflow`: "attempt to shift left with overflow". -/
@[rust_fun "core::panicking::panic_const::panic_const_shl_overflow"]
def core.panicking.panic_const.panic_const_shl_overflow : Result Never :=
  fail .integerOverflow

@[rust_fun "core::panicking::unreachable_display"]
def core.panicking.unreachable_display {T : Type _} (_fmtDisplayInst : core.fmt.Display T) :
  T → Result Never :=
  fun _ => fail .panic

/-! ## `core::default` / `core::marker` -/

@[rust_fun "core::default::{core::default::Default<()>}::default"]
def Tuple.Insts.CoreDefaultDefault.default : Result Unit := ok ()

/-- `PhantomData<T>`: a unit struct. -/
@[reducible, rust_type "core::marker::PhantomData"]
def core.marker.PhantomData (_T : Type u) := Unit

@[rust_fun "core::marker::{core::clone::Clone<core::marker::PhantomData<@T>>}::clone"]
def core.marker.PhantomData.Insts.CoreCloneClone.clone {T : Type _} :
  core.marker.PhantomData T → Result (core.marker.PhantomData T) :=
  fun x => ok x

@[rust_fun "core::marker::{core::default::Default<core::marker::PhantomData<@T>>}::default"]
def core.marker.PhantomData.Insts.CoreDefaultDefault.default (T : Type _) :
  Result (core.marker.PhantomData T) :=
  ok ()

/-! ## `core::mem::size_of` -/

/-- `size_of::<T>()` on the 64-bit targets Cranelift runs on. Lean types are erased, so the
    size comes from an instance selected at the call site: exact for the primitive types, and
    `none` (the fallback instance) for any other type or for a type variable of generic code,
    in which case `size_of` fails with `.undef`. Under monomorphization every call site is
    concrete. -/
class core.mem.SizeOf (T : Type u) where
  size : Option Nat

instance (priority := low) {T : Type u} : core.mem.SizeOf T := ⟨none⟩
instance : core.mem.SizeOf Unit := ⟨some 0⟩
instance : core.mem.SizeOf Bool := ⟨some 1⟩
instance : core.mem.SizeOf Char := ⟨some 4⟩
instance {ty : UScalarTy} : core.mem.SizeOf (UScalar ty) := ⟨some (ty.numBits / 8)⟩
instance {ty : IScalarTy} : core.mem.SizeOf (IScalar ty) := ⟨some (ty.numBits / 8)⟩

@[rust_fun "core::mem::size_of"]
def core.mem.size_of (T : Type _) [inst : core.mem.SizeOf T] : Result Std.Usize :=
  match inst.size with
  | some n => ok (Usize.satOfNat n)
  | none => fail .undef

/-! ## Integer operator impls (`core::ops`), with overflow checks -/

@[rust_fun "core::ops::arith::{core::ops::arith::Add<u32, u32, u32>}::add"]
def U32.Insts.CoreOpsArithAddU32U32.add : Std.U32 → Std.U32 → Result Std.U32 := fun x y => x + y
@[rust_fun "core::ops::arith::{core::ops::arith::Add<usize, usize, usize>}::add"]
def Usize.Insts.CoreOpsArithAddUsizeUsize.add : Std.Usize → Std.Usize → Result Std.Usize :=
  fun x y => x + y
@[rust_fun "core::ops::arith::{core::ops::arith::Add<u16, u16, u16>}::add"]
def U16.Insts.CoreOpsArithAddU16U16.add : Std.U16 → Std.U16 → Result Std.U16 := fun x y => x + y
@[rust_fun "core::ops::arith::{core::ops::arith::Add<u8, u8, u8>}::add"]
def U8.Insts.CoreOpsArithAddU8U8.add : Std.U8 → Std.U8 → Result Std.U8 := fun x y => x + y

@[rust_fun "core::ops::arith::{core::ops::arith::Sub<u32, u32, u32>}::sub"]
def U32.Insts.CoreOpsArithSubU32U32.sub : Std.U32 → Std.U32 → Result Std.U32 := fun x y => x - y
@[rust_fun "core::ops::arith::{core::ops::arith::Sub<usize, usize, usize>}::sub"]
def Usize.Insts.CoreOpsArithSubUsizeUsize.sub : Std.Usize → Std.Usize → Result Std.Usize :=
  fun x y => x - y
@[rust_fun "core::ops::arith::{core::ops::arith::Sub<u16, u16, u16>}::sub"]
def U16.Insts.CoreOpsArithSubU16U16.sub : Std.U16 → Std.U16 → Result Std.U16 := fun x y => x - y
@[rust_fun "core::ops::arith::{core::ops::arith::Sub<u8, u8, u8>}::sub"]
def U8.Insts.CoreOpsArithSubU8U8.sub : Std.U8 → Std.U8 → Result Std.U8 := fun x y => x - y

@[rust_fun "core::ops::bit::{core::ops::bit::Not<u32, u32>}::not"]
def U32.Insts.CoreOpsBitNotU32.not : Std.U32 → Result Std.U32 := fun x => ok (~~~x)
@[rust_fun "core::ops::bit::{core::ops::bit::Not<usize, usize>}::not"]
def Usize.Insts.CoreOpsBitNotUsize.not : Std.Usize → Result Std.Usize := fun x => ok (~~~x)
@[rust_fun "core::ops::bit::{core::ops::bit::Not<u16, u16>}::not"]
def U16.Insts.CoreOpsBitNotU16.not : Std.U16 → Result Std.U16 := fun x => ok (~~~x)
@[rust_fun "core::ops::bit::{core::ops::bit::Not<u8, u8>}::not"]
def U8.Insts.CoreOpsBitNotU8.not : Std.U8 → Result Std.U8 := fun x => ok (~~~x)

@[rust_fun "core::ops::bit::{core::ops::bit::BitAnd<u32, u32, u32>}::bitand"]
def U32.Insts.CoreOpsBitBitAndU32U32.bitand : Std.U32 → Std.U32 → Result Std.U32 :=
  fun x y => ok (x &&& y)
@[rust_fun "core::ops::bit::{core::ops::bit::BitAnd<usize, usize, usize>}::bitand"]
def Usize.Insts.CoreOpsBitBitAndUsizeUsize.bitand : Std.Usize → Std.Usize → Result Std.Usize :=
  fun x y => ok (x &&& y)
@[rust_fun "core::ops::bit::{core::ops::bit::BitAnd<u16, u16, u16>}::bitand"]
def U16.Insts.CoreOpsBitBitAndU16U16.bitand : Std.U16 → Std.U16 → Result Std.U16 :=
  fun x y => ok (x &&& y)
@[rust_fun "core::ops::bit::{core::ops::bit::BitAnd<u8, u8, u8>}::bitand"]
def U8.Insts.CoreOpsBitBitAndU8U8.bitand : Std.U8 → Std.U8 → Result Std.U8 :=
  fun x y => ok (x &&& y)

@[rust_fun "core::ops::bit::{core::ops::bit::BitOr<usize, usize, usize>}::bitor"]
def Usize.Insts.CoreOpsBitBitOrUsizeUsize.bitor : Std.Usize → Std.Usize → Result Std.Usize :=
  fun x y => ok (x ||| y)
@[rust_fun "core::ops::bit::{core::ops::bit::BitOr<u16, u16, u16>}::bitor"]
def U16.Insts.CoreOpsBitBitOrU16U16.bitor : Std.U16 → Std.U16 → Result Std.U16 :=
  fun x y => ok (x ||| y)
@[rust_fun "core::ops::bit::{core::ops::bit::BitOr<u8, u8, u8>}::bitor"]
def U8.Insts.CoreOpsBitBitOrU8U8.bitor : Std.U8 → Std.U8 → Result Std.U8 :=
  fun x y => ok (x ||| y)

@[rust_fun "core::ops::bit::{core::ops::bit::BitXor<&'0 u64, u64, u64>}::bitxor"]
def Shared0U64.Insts.CoreOpsBitBitXorU64U64.bitxor : Std.U64 → Std.U64 → Result Std.U64 :=
  fun x y => ok (x ^^^ y)

/-- Shifts panic ("attempt to shift left/right with overflow") when the amount is at least the
    bit width, as the library's `<<<`/`>>>` do. -/
@[rust_fun "core::ops::bit::{core::ops::bit::Shl<usize, u8, usize>}::shl"]
def Usize.Insts.CoreOpsBitShlU8Usize.shl : Std.Usize → Std.U8 → Result Std.Usize :=
  fun x y => x <<< y
@[rust_fun "core::ops::bit::{core::ops::bit::Shl<u16, u8, u16>}::shl"]
def U16.Insts.CoreOpsBitShlU8U16.shl : Std.U16 → Std.U8 → Result Std.U16 := fun x y => x <<< y
@[rust_fun "core::ops::bit::{core::ops::bit::Shl<u8, u8, u8>}::shl"]
def U8.Insts.CoreOpsBitShlU8U8.shl : Std.U8 → Std.U8 → Result Std.U8 := fun x y => x <<< y
@[rust_fun "core::ops::bit::{core::ops::bit::Shl<u8, &'0 u8, u8>}::shl"]
def U8.Insts.CoreOpsBitShlShared0U8U8.shl : Std.U8 → Std.U8 → Result Std.U8 := fun x y => x <<< y

@[rust_fun "core::ops::bit::{core::ops::bit::Shr<usize, u8, usize>}::shr"]
def Usize.Insts.CoreOpsBitShrU8Usize.shr : Std.Usize → Std.U8 → Result Std.Usize :=
  fun x y => x >>> y
@[rust_fun "core::ops::bit::{core::ops::bit::Shr<u16, u8, u16>}::shr"]
def U16.Insts.CoreOpsBitShrU8U16.shr : Std.U16 → Std.U8 → Result Std.U16 := fun x y => x >>> y
@[rust_fun "core::ops::bit::{core::ops::bit::Shr<u8, u8, u8>}::shr"]
def U8.Insts.CoreOpsBitShrU8U8.shr : Std.U8 → Std.U8 → Result Std.U8 := fun x y => x >>> y

/-! ## `core::ops::range` -/

@[rust_fun "core::ops::range::{core::clone::Clone<core::ops::range::Range<@Idx>>}::clone"]
def core.ops.range.Range.Insts.CoreCloneClone.clone {Idx : Type _}
  (cloneCloneInst : core.clone.Clone Idx) :
  core.ops.range.Range Idx → Result (core.ops.range.Range Idx) :=
  fun r => do
    let s ← cloneCloneInst.clone r.start
    let e ← cloneCloneInst.clone r.«end»
    ok ⟨s, e⟩

/-! ## `core::borrow` / arrays -/

@[rust_fun "core::borrow::{core::borrow::Borrow<&'0 @T, @T>}::borrow"]
def Shared0T.Insts.CoreBorrowBorrow.borrow {T : Type _} : T → Result T :=
  fun x => ok x

@[rust_fun "core::array::{core::borrow::Borrow<[@T; @N], [@T]>}::borrow"]
def Array.Insts.CoreBorrowBorrowSlice.borrow {T : Type _} {N : Std.Usize} :
  Array T N → Result (Slice T) :=
  fun a => ok a.to_slice

@[rust_fun "core::array::{core::borrow::BorrowMut<[@T; @N], [@T]>}::borrow_mut"]
def Array.Insts.CoreBorrowBorrowMutSlice.borrow_mut {T : Type _} {N : Std.Usize} :
  Array T N → Result ((Slice T) × (Slice T → Array T N)) :=
  fun a => ok (a.to_slice, Array.from_slice a)

/-- `usize::to_ne_bytes` on a little-endian 64-bit target. -/
def core.hash.usizeNeBytes (n : Std.Usize) : Slice Std.U8 :=
  let l := (List.range 8).map fun i => ({ bv := BitVec.ofNat _ (n.val / 2 ^ (8 * i)) } : Std.U8)
  if h : l.length ≤ Usize.max then .from l h else .from [] (Nat.zero_le _)

/-- `Hash for [T; N]`: `Hash::hash(&self[..], state)`, i.e. `state.write_length_prefix(len)`
    (`write_usize`, whose provided body writes the native-endian bytes) followed by
    `T::hash_slice`, whose provided body hashes the elements in order. -/
@[rust_fun "core::array::{core::hash::Hash<[@T; @N]>}::hash"]
def Array.Insts.CoreHashHash.hash {T : Type _} {H : Type} {N : Std.Usize}
  (hashHashInst : core.hash.Hash T) (hashHasherInst : core.hash.Hasher H) :
  Array T N → H → Result H :=
  fun a h => do
    let h ← hashHasherInst.write h (core.hash.usizeNeBytes (Usize.satOfNat a.val.length))
    List.foldlM (fun h x => hashHashInst.hash hashHasherInst x h) h a.val

/-- `PartialEq<[U; N]> for [T]`: `false` on a length mismatch, else element-wise `==` in order,
    stopping at the first difference. -/
@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq"]
def Slice.Insts.CoreCmpPartialEqArray.eq {T : Type _} {U : Type _} {N : Std.Usize}
  (cmpPartialEqInst : core.cmp.PartialEq T U) : Slice T → Array U N → Result Bool :=
  fun s a =>
    if s.val.length ≠ a.val.length then ok false
    else List.allM (fun (p : T × U) => cmpPartialEqInst.eq p.1 p.2) (s.val.zip a.val)

/-- `ne`: `!(self == other)` through the slice equality. -/
@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::ne"]
def Slice.Insts.CoreCmpPartialEqArray.ne {T : Type _} {U : Type _} {N : Std.Usize}
  (cmpPartialEqInst : core.cmp.PartialEq T U) : Slice T → Array U N → Result Bool :=
  fun s a => do
    let e ← Slice.Insts.CoreCmpPartialEqArray.eq cmpPartialEqInst s a
    ok (!e)

end Aeneas.Std
