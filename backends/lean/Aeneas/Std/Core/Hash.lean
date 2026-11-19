module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Scalar.Casts
public import Aeneas.Std.Core.Default
public import Aeneas.Std.Slice
public import Aeneas.Std.StringDef
public import Aeneas.Std.RawPtr
public import Aeneas.Data.BitVec
public section

/-!
# `core::hash`

The models follow Rust 1.96 exactly: every `Hash` impl calls the `Hasher` methods in the same
order and with the same arguments as `core`, and `Hasher`'s provided methods have Rust's default
bodies. This matters because hashers such as `FxHasher` override some of the `write_*` methods,
so the hash values (and the iteration order of hash tables) depend on which method is called.
-/

namespace Aeneas.Std

/-- Build a slice from a list (the list is truncated if it exceeds the maximal slice length,
    which cannot happen for the small byte strings built by the models). -/
@[expose] def Slice.ofListClamp {α} (l : List α) : Slice α :=
  if h : l.length ≤ Usize.max then Slice.from l h
  else Slice.from (l.take Usize.max) (by simp)

/-- The little-endian (= native on x86-64/AArch64) bytes of an unsigned integer. -/
@[expose] def UScalar.neBytes {ty} (x : UScalar ty) : List U8 := x.bv.toLEBytes.map UScalar.mk
/-- The little-endian (= native) bytes of a signed integer. -/
@[expose] def IScalar.neBytes {ty} (x : IScalar ty) : List U8 := x.bv.toLEBytes.map UScalar.mk

@[rust_trait "core::hash::Hasher"]
structure core.hash.Hasher (Self : Type _) where
  finish : Self → Result U64
  write : Self → Slice U8 → Result Self
  write_u8 : Self → U8 → Result Self := fun s i => write s (Slice.ofListClamp [i])
  write_u16 : Self → U16 → Result Self := fun s i => write s (Slice.ofListClamp i.neBytes)
  write_u32 : Self → U32 → Result Self := fun s i => write s (Slice.ofListClamp i.neBytes)
  write_u64 : Self → U64 → Result Self := fun s i => write s (Slice.ofListClamp i.neBytes)
  write_u128 : Self → U128 → Result Self := fun s i => write s (Slice.ofListClamp i.neBytes)
  write_usize : Self → Usize → Result Self := fun s i => write s (Slice.ofListClamp i.neBytes)
  write_i8 : Self → I8 → Result Self := fun s i => write_u8 s (IScalar.hcast .U8 i)
  write_i16 : Self → I16 → Result Self := fun s i => write_u16 s (IScalar.hcast .U16 i)
  write_i32 : Self → I32 → Result Self := fun s i => write_u32 s (IScalar.hcast .U32 i)
  write_i64 : Self → I64 → Result Self := fun s i => write_u64 s (IScalar.hcast .U64 i)
  write_i128 : Self → I128 → Result Self := fun s i => write_u128 s (IScalar.hcast .U128 i)
  write_isize : Self → Isize → Result Self := fun s i => write_usize s (IScalar.hcast .Usize i)
  write_length_prefix : Self → Usize → Result Self := fun s len => write_usize s len
  write_str : Self → Str → Result Self := fun s str => do
    let s ← write s str
    write_u8 s ⟨BitVec.ofNat _ 0xff⟩

/-! Default methods of `Hasher` (the instance argument is the instance being defined, so that
    overridden methods are dispatched to, as in Rust). -/

@[expose, trait_default, rust_fun "core::hash::Hasher::write_u8"]
def core.hash.Hasher.write_u8.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : U8) : Result Self := HasherInst.write s (Slice.ofListClamp [i])

@[expose, trait_default, rust_fun "core::hash::Hasher::write_u16"]
def core.hash.Hasher.write_u16.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : U16) : Result Self := HasherInst.write s (Slice.ofListClamp i.neBytes)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_u32"]
def core.hash.Hasher.write_u32.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : U32) : Result Self := HasherInst.write s (Slice.ofListClamp i.neBytes)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_u64"]
def core.hash.Hasher.write_u64.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : U64) : Result Self := HasherInst.write s (Slice.ofListClamp i.neBytes)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_u128"]
def core.hash.Hasher.write_u128.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : U128) : Result Self := HasherInst.write s (Slice.ofListClamp i.neBytes)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_usize"]
def core.hash.Hasher.write_usize.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : Usize) : Result Self := HasherInst.write s (Slice.ofListClamp i.neBytes)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_i8"]
def core.hash.Hasher.write_i8.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : I8) : Result Self := HasherInst.write_u8 s (IScalar.hcast .U8 i)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_i16"]
def core.hash.Hasher.write_i16.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : I16) : Result Self := HasherInst.write_u16 s (IScalar.hcast .U16 i)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_i32"]
def core.hash.Hasher.write_i32.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : I32) : Result Self := HasherInst.write_u32 s (IScalar.hcast .U32 i)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_i64"]
def core.hash.Hasher.write_i64.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : I64) : Result Self := HasherInst.write_u64 s (IScalar.hcast .U64 i)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_i128"]
def core.hash.Hasher.write_i128.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : I128) : Result Self := HasherInst.write_u128 s (IScalar.hcast .U128 i)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_isize"]
def core.hash.Hasher.write_isize.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (i : Isize) : Result Self := HasherInst.write_usize s (IScalar.hcast .Usize i)

@[expose, trait_default, rust_fun "core::hash::Hasher::write_length_prefix"]
def core.hash.Hasher.write_length_prefix.default {Self : Type _}
  (HasherInst : core.hash.Hasher Self) (s : Self) (len : Usize) : Result Self :=
  HasherInst.write_usize s len

@[expose, trait_default, rust_fun "core::hash::Hasher::write_str"]
def core.hash.Hasher.write_str.default {Self : Type _} (HasherInst : core.hash.Hasher Self)
  (s : Self) (str : Str) : Result Self := do
  let s ← HasherInst.write s str
  HasherInst.write_u8 s ⟨BitVec.ofNat _ 0xff⟩

@[rust_trait "core::hash::Hash"]
structure core.hash.Hash (Self : Type _) where
  hash : forall {H : Type}, core.hash.Hasher H → Self → H → Result H
  hash_slice : forall {H : Type}, core.hash.Hasher H → Slice Self → H → Result H :=
    fun {H} HasherInst data state => data.val.foldlM (fun st x => hash HasherInst x st) state

/-- Rust's default `hash_slice`: hash the elements one after the other (no length prefix). -/
@[expose, trait_default, rust_fun "core::hash::Hash::hash_slice"]
def core.hash.Hash.hash_slice.default {Self : Type _} (HashInst : core.hash.Hash Self)
  {H : Type} (HasherInst : core.hash.Hasher H) (data : Slice Self) (state : H) : Result H :=
  data.val.foldlM (fun st x => HashInst.hash HasherInst x st) state

@[rust_trait "core::hash::BuildHasher" (parentClauses := ["HasherInst"])]
structure core.hash.BuildHasher (Self : Type _) (Self_Hasher : Type _) where
  HasherInst : core.hash.Hasher Self_Hasher
  build_hasher : Self → Result Self_Hasher
  hash_one : forall {T : Type}, core.hash.Hash T → Self → T → Result U64 :=
    fun {T} HashInst s x => do
      let h ← build_hasher s
      let h ← HashInst.hash HasherInst x h
      HasherInst.finish h

/-- `BuildHasher::hash_one`: build a hasher, hash the value, finish. -/
@[expose, trait_default, rust_fun "core::hash::BuildHasher::hash_one"]
def core.hash.BuildHasher.hash_one.default {Self : Type _} {Self_Hasher : Type _}
  (BuildHasherInst : core.hash.BuildHasher Self Self_Hasher) {T : Type}
  (HashInst : core.hash.Hash T) (s : Self) (x : T) : Result U64 := do
  let h ← BuildHasherInst.build_hasher s
  let h ← HashInst.hash BuildHasherInst.HasherInst x h
  BuildHasherInst.HasherInst.finish h

/-! ## `BuildHasherDefault<H>` (a `PhantomData<fn() -> H>`) -/

@[expose, rust_type "core::hash::BuildHasherDefault"]
def core.hash.BuildHasherDefault (_H : Type _) : Type := Unit

@[expose, rust_fun
  "core::hash::{core::hash::BuildHasher<core::hash::BuildHasherDefault<@H>, @H>}::build_hasher"]
def core.hash.BuildHasherDefault.Insts.CoreHashBuildHasher.build_hasher {H : Type _}
  (defaultDefaultInst : core.default.Default H) (_HasherInst : core.hash.Hasher H)
  (_ : core.hash.BuildHasherDefault H) : Result H :=
  defaultDefaultInst.default

@[expose, rust_fun "core::hash::{core::clone::Clone<core::hash::BuildHasherDefault<@H>>}::clone"]
def core.hash.BuildHasherDefault.Insts.CoreCloneClone.clone {H : Type _}
  (x : core.hash.BuildHasherDefault H) : Result (core.hash.BuildHasherDefault H) := .ok x

@[expose, rust_fun
  "core::hash::{core::default::Default<core::hash::BuildHasherDefault<@H>>}::default"]
def core.hash.BuildHasherDefault.Insts.CoreDefaultDefault.default (H : Type _) :
  Result (core.hash.BuildHasherDefault H) := .ok ()

/-! ## `Hash` impls of primitive types (`core::hash::impls`) -/

@[expose, rust_fun "core::hash::impls::{core::hash::Hash<u8>}::hash"]
def U8.Insts.CoreHashHash.hash {H : Type _} (HasherInst : core.hash.Hasher H) (x : U8)
  (state : H) : Result H := HasherInst.write_u8 state x

@[expose, rust_fun "core::hash::impls::{core::hash::Hash<u16>}::hash"]
def U16.Insts.CoreHashHash.hash {H : Type _} (HasherInst : core.hash.Hasher H) (x : U16)
  (state : H) : Result H := HasherInst.write_u16 state x

@[expose, rust_fun "core::hash::impls::{core::hash::Hash<u32>}::hash"]
def U32.Insts.CoreHashHash.hash {H : Type _} (HasherInst : core.hash.Hasher H) (x : U32)
  (state : H) : Result H := HasherInst.write_u32 state x

@[expose, rust_fun "core::hash::impls::{core::hash::Hash<u64>}::hash"]
def U64.Insts.CoreHashHash.hash {H : Type _} (HasherInst : core.hash.Hasher H) (x : U64)
  (state : H) : Result H := HasherInst.write_u64 state x

@[expose, rust_fun "core::hash::impls::{core::hash::Hash<usize>}::hash"]
def Usize.Insts.CoreHashHash.hash {H : Type _} (HasherInst : core.hash.Hasher H) (x : Usize)
  (state : H) : Result H := HasherInst.write_usize state x

@[expose, rust_fun "core::hash::impls::{core::hash::Hash<isize>}::hash"]
def Isize.Insts.CoreHashHash.hash {H : Type _} (HasherInst : core.hash.Hasher H) (x : Isize)
  (state : H) : Result H := HasherInst.write_isize state x

/-- `hash_slice` of the integer impls: a single `write` of all the native bytes. -/
@[expose] def core.hash.impls.hashSliceU {ty} {H : Type} (HasherInst : core.hash.Hasher H)
  (data : Slice (UScalar ty)) (state : H) : Result H :=
  HasherInst.write state (Slice.ofListClamp (data.val.flatMap UScalar.neBytes))

@[expose] def core.hash.impls.hashSliceI {ty} {H : Type} (HasherInst : core.hash.Hasher H)
  (data : Slice (IScalar ty)) (state : H) : Result H :=
  HasherInst.write state (Slice.ofListClamp (data.val.flatMap IScalar.neBytes))

@[expose, reducible, rust_trait_impl "core::hash::Hash<u8>"]
def U8.Insts.CoreHashHash : core.hash.Hash U8 := {
  hash := fun HasherInst => U8.Insts.CoreHashHash.hash HasherInst
  hash_slice := fun HasherInst => core.hash.impls.hashSliceU HasherInst }

@[expose, reducible, rust_trait_impl "core::hash::Hash<u16>"]
def U16.Insts.CoreHashHash : core.hash.Hash U16 := {
  hash := fun HasherInst => U16.Insts.CoreHashHash.hash HasherInst
  hash_slice := fun HasherInst => core.hash.impls.hashSliceU HasherInst }

@[expose, reducible, rust_trait_impl "core::hash::Hash<u32>"]
def U32.Insts.CoreHashHash : core.hash.Hash U32 := {
  hash := fun HasherInst => U32.Insts.CoreHashHash.hash HasherInst
  hash_slice := fun HasherInst => core.hash.impls.hashSliceU HasherInst }

@[expose, reducible, rust_trait_impl "core::hash::Hash<u64>"]
def U64.Insts.CoreHashHash : core.hash.Hash U64 := {
  hash := fun HasherInst => U64.Insts.CoreHashHash.hash HasherInst
  hash_slice := fun HasherInst => core.hash.impls.hashSliceU HasherInst }

@[expose, reducible, rust_trait_impl "core::hash::Hash<usize>"]
def Usize.Insts.CoreHashHash : core.hash.Hash Usize := {
  hash := fun HasherInst => Usize.Insts.CoreHashHash.hash HasherInst
  hash_slice := fun HasherInst => core.hash.impls.hashSliceU HasherInst }

@[expose, reducible, rust_trait_impl "core::hash::Hash<isize>"]
def Isize.Insts.CoreHashHash : core.hash.Hash Isize := {
  hash := fun HasherInst => Isize.Insts.CoreHashHash.hash HasherInst
  hash_slice := fun HasherInst => core.hash.impls.hashSliceI HasherInst }

/-- Tuples: the components in order (no separator). -/
@[expose, rust_fun "core::hash::impls::{core::hash::Hash<(@T, @B)>}::hash"]
def Pair.Insts.CoreHashHash.hash {T : Type _} {B : Type _} {S : Type _}
  (HashInst : core.hash.Hash T) (HashInst1 : core.hash.Hash B)
  (HasherInst : core.hash.Hasher S) (x : T × B) (state : S) : Result S := do
  let state ← HashInst.hash HasherInst x.1 state
  HashInst1.hash HasherInst x.2 state

/-- Rust hashes the address of the pointer (`write_usize(addr)`) and its metadata. Raw pointers
    carry no address in this model, so hashing them is not supported. -/
@[expose, rust_fun "core::hash::impls::{core::hash::Hash<*const @T>}::hash"]
def RawPtrConstT.Insts.CoreHashHash.hash {T : Type _} {H : Type _}
  (_HasherInst : core.hash.Hasher H) (_ : ConstRawPtr T) (_ : H) : Result H :=
  .fail .undef

end Aeneas.Std
