/- `std::hash::random`: `RandomState` and `DefaultHasher` (SipHash-1-3).

Rust seeds every `RandomState` with per-thread random keys (and increments `k0` at every
`RandomState::new`). The model is deterministic: every `RandomState` has the keys `(0, 0)`, so
`DefaultHasher` computes exactly the hashes of Rust's `DefaultHasher::new()` (SipHash-1-3, keys
`(0, 0)`), with Rust's streaming semantics (`write` calls are concatenated). -/
module
public import Aeneas.Std.Core.Hash
public import Aeneas.Std.Core.Default
public section

namespace Aeneas.Std

open Result

@[rust_type "std::hash::random::RandomState" (body := .opaque)]
structure std.hash.random.RandomState where
  k0 : UInt64
  k1 : UInt64

/-- SipHash-1-3 state (`core::hash::sip::Hasher<Sip13Rounds>`): keys, `v0..v3`, the pending
    tail bytes (little-endian, `ntail < 8` of them) and the total length written. -/
@[rust_type "std::hash::random::DefaultHasher" (body := .opaque)]
structure std.hash.random.DefaultHasher where
  k0 : UInt64
  k1 : UInt64
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  tail : UInt64
  ntail : Nat
  length : Nat

namespace SipModel

@[expose] def rotl (x : UInt64) (n : UInt64) : UInt64 := (x <<< n) ||| (x >>> (64 - n))

/-- One SipHash round (`compress!`). -/
@[expose] def compress (v : UInt64 × UInt64 × UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let (v0, v1, v2, v3) := v
  let v0 := v0 + v1
  let v2 := v2 + v3
  let v1 := rotl v1 13
  let v1 := v1 ^^^ v0
  let v3 := rotl v3 16
  let v3 := v3 ^^^ v2
  let v0 := rotl v0 32
  let v2 := v2 + v1
  let v0 := v0 + v3
  let v1 := rotl v1 17
  let v1 := v1 ^^^ v2
  let v3 := rotl v3 21
  let v3 := v3 ^^^ v0
  let v2 := rotl v2 32
  (v0, v1, v2, v3)

@[expose] def new (k0 k1 : UInt64) : std.hash.random.DefaultHasher :=
  { k0, k1,
    v0 := k0 ^^^ 0x736f6d6570736575, v1 := k1 ^^^ 0x646f72616e646f6d,
    v2 := k0 ^^^ 0x6c7967656e657261, v3 := k1 ^^^ 0x7465646279746573,
    tail := 0, ntail := 0, length := 0 }

/-- Absorb one byte (equivalent to Rust's block-wise `write`). -/
@[expose] def writeByte (h : std.hash.random.DefaultHasher) (b : UInt64) :
    std.hash.random.DefaultHasher :=
  let tail := h.tail ||| (b <<< (8 * h.ntail.toUInt64))
  if h.ntail + 1 = 8 then
    let (v0, v1, v2, v3) := compress (h.v0, h.v1, h.v2, h.v3 ^^^ tail)
    { h with v0 := v0 ^^^ tail, v1, v2, v3, tail := 0, ntail := 0, length := h.length + 1 }
  else { h with tail, ntail := h.ntail + 1, length := h.length + 1 }

@[expose] def finish (h : std.hash.random.DefaultHasher) : UInt64 :=
  let b : UInt64 := ((h.length.toUInt64 &&& 0xff) <<< 56) ||| h.tail
  let (v0, v1, v2, v3) := compress (h.v0, h.v1, h.v2, h.v3 ^^^ b)
  let (v0, v1, v2, v3) := (v0 ^^^ b, v1, v2 ^^^ 0xff, v3)
  let (v0, v1, v2, v3) := compress (compress (compress (v0, v1, v2, v3)))
  v0 ^^^ v1 ^^^ v2 ^^^ v3

end SipModel

@[expose, rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
    (h : std.hash.random.DefaultHasher) : Result Std.U64 :=
  ok { bv := (SipModel.finish h).toBitVec }

@[expose, rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
    (h : std.hash.random.DefaultHasher) (msg : Slice Std.U8) :
    Result std.hash.random.DefaultHasher :=
  ok (msg.val.foldl (fun h b => SipModel.writeByte h b.bv.toNat.toUInt64) h)

@[expose, rust_fun
  "std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher"]
def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
    (s : std.hash.random.RandomState) : Result std.hash.random.DefaultHasher :=
  ok (SipModel.new s.k0 s.k1)

/-- Deterministic: keys `(0, 0)` (see the module documentation). -/
@[expose, rust_fun "std::hash::random::{core::default::Default<std::hash::random::RandomState>}::default"]
def std.hash.random.RandomState.Insts.CoreDefaultDefault.default :
    Result std.hash.random.RandomState :=
  ok { k0 := 0, k1 := 0 }

/-- `DefaultHasher::new()`: SipHash-1-3 with keys `(0, 0)`. -/
@[expose, rust_fun "std::hash::random::{std::hash::random::DefaultHasher}::new"]
def std.hash.random.DefaultHasher.new : Result std.hash.random.DefaultHasher :=
  ok (SipModel.new 0 0)

end Aeneas.Std
