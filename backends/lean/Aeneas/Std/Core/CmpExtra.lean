module
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.RawPtr
public section

@[expose] section

/-! `core::cmp` / `core::tuple` comparison impls (Rust 1.96). -/

namespace Aeneas.Std

open Result

@[rust_fun "core::cmp::{core::cmp::PartialEq<core::cmp::Ordering, core::cmp::Ordering>}::eq"]
def core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq : Ordering → Ordering → Result Bool :=
  fun a b => ok (decide (a = b))

@[rust_fun "core::cmp::impls::{core::cmp::PartialEq<char, char>}::eq"]
def Char.Insts.CoreCmpPartialEqChar.eq : Char → Char → Result Bool :=
  fun a b => ok (decide (a = b))

@[rust_fun "core::cmp::impls::{core::cmp::PartialEq<char, char>}::ne"]
def Char.Insts.CoreCmpPartialEqChar.ne : Char → Char → Result Bool :=
  fun a b => ok (decide (a ≠ b))

/-- `PartialOrd for bool`: `false < true`. -/
@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<bool, bool>}::partial_cmp"]
def Bool.Insts.CoreCmpPartialOrdBool.partial_cmp : Bool → Bool → Result (Option Ordering) :=
  fun a b => ok (some (compare a.toNat b.toNat))

/-! ## `Reverse` -/

/-- `core::cmp::Reverse<T>(pub T)`: a single-field tuple struct, represented by its field (as
    Aeneas does for such structs). -/
@[reducible, rust_type "core::cmp::Reverse"]
def core.cmp.Reverse (T : Type u) := T

@[rust_fun "core::cmp::{core::cmp::PartialEq<core::cmp::Reverse<@T>, core::cmp::Reverse<@T>>}::eq"]
def core.cmp.Reverse.Insts.CoreCmpPartialEqReverse.eq {T : Type _}
  (PartialEqInst : core.cmp.PartialEq T T) :
  core.cmp.Reverse T → core.cmp.Reverse T → Result Bool :=
  fun a b => PartialEqInst.eq a b

@[rust_fun "core::cmp::{core::cmp::Eq<core::cmp::Reverse<@T>>}::assert_fields_are_eq"]
def core.cmp.Reverse.Insts.CoreCmpEq.assert_fields_are_eq {T : Type _}
  (_EqInst : core.cmp.Eq T) : core.cmp.Reverse T → Result Unit :=
  fun _ => ok ()

/-- `Reverse::partial_cmp`: `other.0.partial_cmp(&self.0)`. -/
@[rust_fun
  "core::cmp::{core::cmp::PartialOrd<core::cmp::Reverse<@T>, core::cmp::Reverse<@T>>}::partial_cmp"]
def core.cmp.Reverse.Insts.CoreCmpPartialOrdReverse.partial_cmp {T : Type _}
  (PartialOrdInst : core.cmp.PartialOrd T T) :
  core.cmp.Reverse T → core.cmp.Reverse T → Result (Option Ordering) :=
  fun a b => PartialOrdInst.partial_cmp b a

/-- `Reverse::lt`: `other.0 < self.0`. -/
@[rust_fun "core::cmp::{core::cmp::PartialOrd<core::cmp::Reverse<@T>, core::cmp::Reverse<@T>>}::lt"]
def core.cmp.Reverse.Insts.CoreCmpPartialOrdReverse.lt {T : Type _}
  (PartialOrdInst : core.cmp.PartialOrd T T) :
  core.cmp.Reverse T → core.cmp.Reverse T → Result Bool :=
  fun a b => PartialOrdInst.lt b a

@[rust_fun "core::cmp::{core::cmp::PartialOrd<core::cmp::Reverse<@T>, core::cmp::Reverse<@T>>}::le"]
def core.cmp.Reverse.Insts.CoreCmpPartialOrdReverse.le {T : Type _}
  (PartialOrdInst : core.cmp.PartialOrd T T) :
  core.cmp.Reverse T → core.cmp.Reverse T → Result Bool :=
  fun a b => PartialOrdInst.le b a

@[rust_fun "core::cmp::{core::cmp::PartialOrd<core::cmp::Reverse<@T>, core::cmp::Reverse<@T>>}::gt"]
def core.cmp.Reverse.Insts.CoreCmpPartialOrdReverse.gt {T : Type _}
  (PartialOrdInst : core.cmp.PartialOrd T T) :
  core.cmp.Reverse T → core.cmp.Reverse T → Result Bool :=
  fun a b => PartialOrdInst.gt b a

@[rust_fun "core::cmp::{core::cmp::PartialOrd<core::cmp::Reverse<@T>, core::cmp::Reverse<@T>>}::ge"]
def core.cmp.Reverse.Insts.CoreCmpPartialOrdReverse.ge {T : Type _}
  (PartialOrdInst : core.cmp.PartialOrd T T) :
  core.cmp.Reverse T → core.cmp.Reverse T → Result Bool :=
  fun a b => PartialOrdInst.ge b a

/-- `Reverse::cmp`: `other.0.cmp(&self.0)`. -/
@[rust_fun "core::cmp::{core::cmp::Ord<core::cmp::Reverse<@T>>}::cmp"]
def core.cmp.Reverse.Insts.CoreCmpOrd.cmp {T : Type _} (OrdInst : core.cmp.Ord T) :
  core.cmp.Reverse T → core.cmp.Reverse T → Result Ordering :=
  fun a b => OrdInst.cmp b a

/-! ## Tuples

`eq` is `a.0 == b.0 && a.1 == b.1 && ...`, `ne` is `a.0 != b.0 || ...` (short-circuiting),
`partial_cmp`/`cmp` are lexicographic, and `lt`/`le`/`gt`/`ge` chain through
`partial_cmp` of the leading components (`__chaining_*`, `Continue` on `Equal`) and use the
relation itself on the last component. -/

/-- One step of `__chaining_<rel>`: `none` = `Continue(())`, `some b` = `Break(b)`. -/
def core.tuple.chain {T : Type u} (inst : core.cmp.PartialOrd T T) (rel : Ordering → Bool)
    (a b : T) : Result (Option Bool) := do
  let c ← inst.partial_cmp a b
  match c with
  | some .eq => ok none
  | some c => ok (some (rel c))
  | none => ok (some false)

def core.tuple.lexRel2 {U : Type u} {T : Type v} (i0 : core.cmp.PartialOrd U U)
    (rel : Ordering → Bool) (last : T → T → Result Bool) (a b : U × T) : Result Bool := do
  let r ← core.tuple.chain i0 rel a.1 b.1
  match r with
  | some v => ok v
  | none => last a.2 b.2

@[rust_fun "core::tuple::{core::cmp::PartialEq<(@U, @T), (@U, @T)>}::eq"]
def Pair.Insts.CoreCmpPartialEqPair.eq {U : Type _} {T : Type _}
  (cmpPartialEqInst : core.cmp.PartialEq U U) (cmpPartialEqInst1 : core.cmp.PartialEq T T) :
  (U × T) → (U × T) → Result Bool :=
  fun a b => do
    let e ← cmpPartialEqInst.eq a.1 b.1
    if e then cmpPartialEqInst1.eq a.2 b.2 else ok false

@[rust_fun "core::tuple::{core::cmp::PartialEq<(@U, @T), (@U, @T)>}::ne"]
def Pair.Insts.CoreCmpPartialEqPair.ne {U : Type _} {T : Type _}
  (cmpPartialEqInst : core.cmp.PartialEq U U) (cmpPartialEqInst1 : core.cmp.PartialEq T T) :
  (U × T) → (U × T) → Result Bool :=
  fun a b => do
    let n ← cmpPartialEqInst.ne a.1 b.1
    if n then ok true else cmpPartialEqInst1.ne a.2 b.2

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@U, @T), (@U, @T)>}::partial_cmp"]
def Pair.Insts.CoreCmpPartialOrdPair.partial_cmp {U : Type _} {T : Type _}
  (cmpPartialOrdInst : core.cmp.PartialOrd U U) (cmpPartialOrdInst1 : core.cmp.PartialOrd T T) :
  (U × T) → (U × T) → Result (Option Ordering) :=
  fun a b => do
    let c ← cmpPartialOrdInst.partial_cmp a.1 b.1
    match c with
    | some .eq => cmpPartialOrdInst1.partial_cmp a.2 b.2
    | c => ok c

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@U, @T), (@U, @T)>}::lt"]
def Pair.Insts.CoreCmpPartialOrdPair.lt {U : Type _} {T : Type _}
  (cmpPartialOrdInst : core.cmp.PartialOrd U U) (cmpPartialOrdInst1 : core.cmp.PartialOrd T T) :
  (U × T) → (U × T) → Result Bool :=
  core.tuple.lexRel2 cmpPartialOrdInst (· == .lt) cmpPartialOrdInst1.lt

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@U, @T), (@U, @T)>}::le"]
def Pair.Insts.CoreCmpPartialOrdPair.le {U : Type _} {T : Type _}
  (cmpPartialOrdInst : core.cmp.PartialOrd U U) (cmpPartialOrdInst1 : core.cmp.PartialOrd T T) :
  (U × T) → (U × T) → Result Bool :=
  core.tuple.lexRel2 cmpPartialOrdInst (· != .gt) cmpPartialOrdInst1.le

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@U, @T), (@U, @T)>}::gt"]
def Pair.Insts.CoreCmpPartialOrdPair.gt {U : Type _} {T : Type _}
  (cmpPartialOrdInst : core.cmp.PartialOrd U U) (cmpPartialOrdInst1 : core.cmp.PartialOrd T T) :
  (U × T) → (U × T) → Result Bool :=
  core.tuple.lexRel2 cmpPartialOrdInst (· == .gt) cmpPartialOrdInst1.gt

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@U, @T), (@U, @T)>}::ge"]
def Pair.Insts.CoreCmpPartialOrdPair.ge {U : Type _} {T : Type _}
  (cmpPartialOrdInst : core.cmp.PartialOrd U U) (cmpPartialOrdInst1 : core.cmp.PartialOrd T T) :
  (U × T) → (U × T) → Result Bool :=
  core.tuple.lexRel2 cmpPartialOrdInst (· != .lt) cmpPartialOrdInst1.ge

@[rust_fun "core::tuple::{core::cmp::Ord<(@U, @T)>}::cmp"]
def Pair.Insts.CoreCmpOrd.cmp {U : Type _} {T : Type _}
  (cmpOrdInst : core.cmp.Ord U) (cmpOrdInst1 : core.cmp.Ord T) :
  (U × T) → (U × T) → Result Ordering :=
  fun a b => do
    let c ← cmpOrdInst.cmp a.1 b.1
    match c with
    | .eq => cmpOrdInst1.cmp a.2 b.2
    | c => ok c

@[rust_fun "core::tuple::{core::cmp::PartialEq<(@V, @U, @T), (@V, @U, @T)>}::eq"]
def TupleVUT.Insts.CoreCmpPartialEqTupleVUT.eq {V : Type _} {U : Type _} {T : Type _}
  (cmpPartialEqInst : core.cmp.PartialEq V V) (cmpPartialEqInst1 : core.cmp.PartialEq U U)
  (cmpPartialEqInst2 : core.cmp.PartialEq T T) :
  (V × U × T) → (V × U × T) → Result Bool :=
  fun a b => do
    let e ← cmpPartialEqInst.eq a.1 b.1
    if e then Pair.Insts.CoreCmpPartialEqPair.eq cmpPartialEqInst1 cmpPartialEqInst2 a.2 b.2
    else ok false

@[rust_fun "core::tuple::{core::cmp::PartialEq<(@V, @U, @T), (@V, @U, @T)>}::ne"]
def TupleVUT.Insts.CoreCmpPartialEqTupleVUT.ne {V : Type _} {U : Type _} {T : Type _}
  (cmpPartialEqInst : core.cmp.PartialEq V V) (cmpPartialEqInst1 : core.cmp.PartialEq U U)
  (cmpPartialEqInst2 : core.cmp.PartialEq T T) :
  (V × U × T) → (V × U × T) → Result Bool :=
  fun a b => do
    let n ← cmpPartialEqInst.ne a.1 b.1
    if n then ok true
    else Pair.Insts.CoreCmpPartialEqPair.ne cmpPartialEqInst1 cmpPartialEqInst2 a.2 b.2

@[rust_fun "core::tuple::{core::cmp::PartialEq<(@W, @V, @U, @T), (@W, @V, @U, @T)>}::eq"]
def TupleWVUT.Insts.CoreCmpPartialEqTupleWVUT.eq {W : Type _} {V : Type _} {U : Type _}
  {T : Type _} (cmpPartialEqInst : core.cmp.PartialEq W W)
  (cmpPartialEqInst1 : core.cmp.PartialEq V V) (cmpPartialEqInst2 : core.cmp.PartialEq U U)
  (cmpPartialEqInst3 : core.cmp.PartialEq T T) :
  (W × V × U × T) → (W × V × U × T) → Result Bool :=
  fun a b => do
    let e ← cmpPartialEqInst.eq a.1 b.1
    if e then
      TupleVUT.Insts.CoreCmpPartialEqTupleVUT.eq cmpPartialEqInst1 cmpPartialEqInst2
        cmpPartialEqInst3 a.2 b.2
    else ok false

@[rust_fun "core::tuple::{core::cmp::PartialEq<(@W, @V, @U, @T), (@W, @V, @U, @T)>}::ne"]
def TupleWVUT.Insts.CoreCmpPartialEqTupleWVUT.ne {W : Type _} {V : Type _} {U : Type _}
  {T : Type _} (cmpPartialEqInst : core.cmp.PartialEq W W)
  (cmpPartialEqInst1 : core.cmp.PartialEq V V) (cmpPartialEqInst2 : core.cmp.PartialEq U U)
  (cmpPartialEqInst3 : core.cmp.PartialEq T T) :
  (W × V × U × T) → (W × V × U × T) → Result Bool :=
  fun a b => do
    let n ← cmpPartialEqInst.ne a.1 b.1
    if n then ok true
    else
      TupleVUT.Insts.CoreCmpPartialEqTupleVUT.ne cmpPartialEqInst1 cmpPartialEqInst2
        cmpPartialEqInst3 a.2 b.2

/-- Lexicographic `__chaining` relation over a 4-tuple. -/
def core.tuple.lexRel4 {W : Type u} {V : Type v} {U : Type w} {T : Type x}
    (i0 : core.cmp.PartialOrd W W) (i1 : core.cmp.PartialOrd V V) (i2 : core.cmp.PartialOrd U U)
    (rel : Ordering → Bool) (last : T → T → Result Bool) (a b : W × V × U × T) :
    Result Bool := do
  let r ← core.tuple.chain i0 rel a.1 b.1
  match r with
  | some v => ok v
  | none => do
    let r ← core.tuple.chain i1 rel a.2.1 b.2.1
    match r with
    | some v => ok v
    | none => core.tuple.lexRel2 i2 rel last a.2.2 b.2.2

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@W, @V, @U, @T), (@W, @V, @U, @T)>}::partial_cmp"]
def TupleWVUT.Insts.CoreCmpPartialOrdTupleWVUT.partial_cmp {W : Type _} {V : Type _}
  {U : Type _} {T : Type _} (cmpPartialOrdInst : core.cmp.PartialOrd W W)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd V V) (cmpPartialOrdInst2 : core.cmp.PartialOrd U U)
  (cmpPartialOrdInst3 : core.cmp.PartialOrd T T) :
  (W × V × U × T) → (W × V × U × T) → Result (Option Ordering) :=
  fun a b => do
    let c ← cmpPartialOrdInst.partial_cmp a.1 b.1
    match c with
    | some .eq => do
      let c ← cmpPartialOrdInst1.partial_cmp a.2.1 b.2.1
      match c with
      | some .eq =>
        Pair.Insts.CoreCmpPartialOrdPair.partial_cmp cmpPartialOrdInst2 cmpPartialOrdInst3
          a.2.2 b.2.2
      | c => ok c
    | c => ok c

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@W, @V, @U, @T), (@W, @V, @U, @T)>}::lt"]
def TupleWVUT.Insts.CoreCmpPartialOrdTupleWVUT.lt {W : Type _} {V : Type _} {U : Type _}
  {T : Type _} (cmpPartialOrdInst : core.cmp.PartialOrd W W)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd V V) (cmpPartialOrdInst2 : core.cmp.PartialOrd U U)
  (cmpPartialOrdInst3 : core.cmp.PartialOrd T T) :
  (W × V × U × T) → (W × V × U × T) → Result Bool :=
  core.tuple.lexRel4 cmpPartialOrdInst cmpPartialOrdInst1 cmpPartialOrdInst2 (· == .lt)
    cmpPartialOrdInst3.lt

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@W, @V, @U, @T), (@W, @V, @U, @T)>}::le"]
def TupleWVUT.Insts.CoreCmpPartialOrdTupleWVUT.le {W : Type _} {V : Type _} {U : Type _}
  {T : Type _} (cmpPartialOrdInst : core.cmp.PartialOrd W W)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd V V) (cmpPartialOrdInst2 : core.cmp.PartialOrd U U)
  (cmpPartialOrdInst3 : core.cmp.PartialOrd T T) :
  (W × V × U × T) → (W × V × U × T) → Result Bool :=
  core.tuple.lexRel4 cmpPartialOrdInst cmpPartialOrdInst1 cmpPartialOrdInst2 (· != .gt)
    cmpPartialOrdInst3.le

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@W, @V, @U, @T), (@W, @V, @U, @T)>}::gt"]
def TupleWVUT.Insts.CoreCmpPartialOrdTupleWVUT.gt {W : Type _} {V : Type _} {U : Type _}
  {T : Type _} (cmpPartialOrdInst : core.cmp.PartialOrd W W)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd V V) (cmpPartialOrdInst2 : core.cmp.PartialOrd U U)
  (cmpPartialOrdInst3 : core.cmp.PartialOrd T T) :
  (W × V × U × T) → (W × V × U × T) → Result Bool :=
  core.tuple.lexRel4 cmpPartialOrdInst cmpPartialOrdInst1 cmpPartialOrdInst2 (· == .gt)
    cmpPartialOrdInst3.gt

@[rust_fun "core::tuple::{core::cmp::PartialOrd<(@W, @V, @U, @T), (@W, @V, @U, @T)>}::ge"]
def TupleWVUT.Insts.CoreCmpPartialOrdTupleWVUT.ge {W : Type _} {V : Type _} {U : Type _}
  {T : Type _} (cmpPartialOrdInst : core.cmp.PartialOrd W W)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd V V) (cmpPartialOrdInst2 : core.cmp.PartialOrd U U)
  (cmpPartialOrdInst3 : core.cmp.PartialOrd T T) :
  (W × V × U × T) → (W × V × U × T) → Result Bool :=
  core.tuple.lexRel4 cmpPartialOrdInst cmpPartialOrdInst1 cmpPartialOrdInst2 (· != .lt)
    cmpPartialOrdInst3.ge

@[rust_fun "core::tuple::{core::cmp::Ord<(@W, @V, @U, @T)>}::cmp"]
def TupleWVUT.Insts.CoreCmpOrd.cmp {W : Type _} {V : Type _} {U : Type _} {T : Type _}
  (cmpOrdInst : core.cmp.Ord W) (cmpOrdInst1 : core.cmp.Ord V) (cmpOrdInst2 : core.cmp.Ord U)
  (cmpOrdInst3 : core.cmp.Ord T) :
  (W × V × U × T) → (W × V × U × T) → Result Ordering :=
  fun a b => do
    let c ← cmpOrdInst.cmp a.1 b.1
    match c with
    | .eq => do
      let c ← cmpOrdInst1.cmp a.2.1 b.2.1
      match c with
      | .eq => Pair.Insts.CoreCmpOrd.cmp cmpOrdInst2 cmpOrdInst3 a.2.2 b.2.2
      | c => ok c
    | c => ok c

/-- `*const T == *const T` compares addresses. The raw pointer model (`RawPtr`) has no
    addresses, so the comparison is not expressible: it fails with `.undef`. -/
@[rust_fun "core::ptr::const_ptr::{core::cmp::PartialEq<*const @T, *const @T>}::eq"]
def RawPtrConstT.Insts.CoreCmpPartialEqRawPtrConstT.eq {T : Type _} :
  ConstRawPtr T → ConstRawPtr T → Result Bool :=
  fun _ _ => fail .undef

end Aeneas.Std
