module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Result
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.Core.Hash
public import Aeneas.Std.Slice
public import Aeneas.Std.StringDef
public import Aeneas.Std.RawPtr
public import Aeneas.Std.Range
public section

/-!
# `core::str` (Rust 1.96)

`str` is `Str` (= `Slice U8`, its UTF-8 bytes). The models work on the byte lists and follow
Rust's algorithms step by step where the observable results depend on them (UTF-8 validation
errors, the `SearchStep` sequences of `CharSearcher` and of the Two-Way `StrSearcher`).
Rust `str`s are valid UTF-8; functions which are undefined behaviour on other inputs (or on
non-char-boundary indices in `get_unchecked`) fail with `.undef`.
-/

namespace Aeneas.Std

open Result

/-! ## Bytes and UTF-8 -/

@[expose] def Str.bytes (s : Str) : List Nat := (Slice.val (α := U8) s).map (·.val)

@[expose] def Str.ofBytes (l : List Nat) : Str :=
  Slice.ofListClamp (l.map (fun b => (⟨BitVec.ofNat _ b⟩ : U8)))

@[expose] def Usize.ofNatWrap (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩

/-- Whether `b` is a UTF-8 continuation byte (`b as i8 < -64`). -/
@[expose] def utf8IsCont (b : Nat) : Bool := 0x80 ≤ b && b < 0xC0

/-- Decode the first character of valid UTF-8 bytes: the character and its width. -/
@[expose] def utf8First (bs : List Nat) : Option (Char × Nat) :=
  match bs with
  | [] => none
  | b0 :: rest =>
    if b0 < 0x80 then some (Char.ofNat b0, 1)
    else if b0 < 0xE0 then
      let b1 := rest.headD 0
      some (Char.ofNat ((b0 % 32) * 64 + b1 % 64), 2)
    else if b0 < 0xF0 then
      let b1 := rest.headD 0
      let b2 := (rest.drop 1).headD 0
      some (Char.ofNat ((b0 % 16) * 4096 + (b1 % 64) * 64 + b2 % 64), 3)
    else
      let b1 := rest.headD 0
      let b2 := (rest.drop 1).headD 0
      let b3 := (rest.drop 2).headD 0
      some (Char.ofNat ((b0 % 8) * 262144 + (b1 % 64) * 4096 + (b2 % 64) * 64 + b3 % 64), 4)

/-- Decode the last character of valid UTF-8 bytes: the character and its width. -/
@[expose] def utf8Last (bs : List Nat) : Option (Char × Nat) :=
  let n := bs.length
  if n == 0 then none else
  let w := if utf8IsCont (bs.getD (n - 1) 0) then
      if utf8IsCont (bs.getD (n - 2) 0) then
        if utf8IsCont (bs.getD (n - 3) 0) then 4 else 3
      else 2
    else 1
  utf8First (bs.drop (n - w))

/-- The UTF-8 encoding of a character. -/
@[expose] def utf8Encode (c : Char) : List Nat :=
  c.toString.toUTF8.toList.map (·.toNat)

/-- `str::is_char_boundary`. -/
@[expose] def Str.isCharBoundary (bs : List Nat) (i : Nat) : Bool :=
  if i == 0 then true
  else if i < bs.length then !utf8IsCont (bs.getD i 0)
  else i == bs.length

/-- `char::is_whitespace` (Unicode `White_Space`). -/
@[expose] def core.char.isWhitespace (c : Char) : Bool :=
  let x := c.toNat
  (0x09 ≤ x && x ≤ 0x0D) || x == 0x20 || x == 0x85 || x == 0xA0 || x == 0x1680 ||
  (0x2000 ≤ x && x ≤ 0x200A) || x == 0x2028 || x == 0x2029 || x == 0x202F || x == 0x205F ||
  x == 0x3000

/-! ## UTF-8 validation (`core::str::from_utf8`) -/

@[rust_type "core::str::error::Utf8Error" (body := .opaque)]
structure core.str.error.Utf8Error where
  valid_up_to : Usize
  error_len : Option U8
deriving Inhabited

/-- `run_utf8_validation`: `none` if valid, otherwise `(valid_up_to, error_len)`. -/
@[expose] def utf8Validate (bs : List Nat) : Option (Nat × Option Nat) :=
  let rec go (offset : Nat) (bs : List Nat) : Option (Nat × Option Nat) :=
    match bs with
    | [] => none
    | first :: rest =>
      if first < 0x80 then go (offset + 1) rest
      else
        let w := if 0xC2 ≤ first && first ≤ 0xDF then 2
          else if 0xE0 ≤ first && first ≤ 0xEF then 3
          else if 0xF0 ≤ first && first ≤ 0xF4 then 4 else 0
        let err (l : Option Nat) := some (offset, l)
        match w, rest with
        | 2, [] => err none
        | 2, b1 :: rest => if !utf8IsCont b1 then err (some 1) else go (offset + 2) rest
        | 3, [] => err none
        | 3, b1 :: rest =>
          let ok1 := (first == 0xE0 && 0xA0 ≤ b1 && b1 ≤ 0xBF) ||
            (0xE1 ≤ first && first ≤ 0xEC && utf8IsCont b1) ||
            (first == 0xED && 0x80 ≤ b1 && b1 ≤ 0x9F) ||
            (0xEE ≤ first && first ≤ 0xEF && utf8IsCont b1)
          if !ok1 then err (some 1) else
          match rest with
          | [] => err none
          | b2 :: rest => if !utf8IsCont b2 then err (some 2) else go (offset + 3) rest
        | 4, [] => err none
        | 4, b1 :: rest =>
          let ok1 := (first == 0xF0 && 0x90 ≤ b1 && b1 ≤ 0xBF) ||
            (0xF1 ≤ first && first ≤ 0xF3 && utf8IsCont b1) ||
            (first == 0xF4 && 0x80 ≤ b1 && b1 ≤ 0x8F)
          if !ok1 then err (some 1) else
          match rest with
          | [] => err none
          | b2 :: rest =>
            if !utf8IsCont b2 then err (some 2) else
            match rest with
            | [] => err none
            | b3 :: rest => if !utf8IsCont b3 then err (some 3) else go (offset + 4) rest
        | _, _ => err (some 1)
  go 0 bs

@[expose, rust_fun "core::str::converts::from_utf8"]
def core.str.converts.from_utf8 (v : Slice U8) :
    Result (core.result.Result Str core.str.error.Utf8Error) :=
  match utf8Validate (Str.bytes v) with
  | none => ok (.Ok v)
  | some (validUpTo, errLen) =>
    ok (.Err { valid_up_to := Usize.ofNatWrap validUpTo,
               error_len := errLen.map (fun l => ⟨BitVec.ofNat _ l⟩) })

/-! ## Basic methods -/

@[expose, rust_fun "core::str::{str}::len"]
def core.str.Str.len (s : Str) : Result Usize := ok (Usize.ofNatWrap (Str.bytes s).length)

@[expose, rust_fun "core::str::{str}::is_empty"]
def core.str.Str.is_empty (s : Str) : Result Bool := ok (Str.bytes s).isEmpty

@[expose, rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (s : Str) : Result (Slice U8) := ok s

@[expose, rust_fun "core::str::{core::convert::AsRef<str, [u8]>}::as_ref"]
def Str.Insts.CoreConvertAsRefSliceU8.as_ref (s : Str) : Result (Slice U8) := ok s

@[expose, rust_fun "core::str::traits::{core::cmp::PartialEq<str, str>}::eq"]
def Str.Insts.CoreCmpPartialEqStr.eq (a b : Str) : Result Bool := ok (Str.bytes a == Str.bytes b)

/-- Panics if `mid` is not on a char boundary ("byte index is not a char boundary"). -/
@[expose, rust_fun "core::str::{str}::split_at"]
def core.str.Str.split_at (s : Str) (mid : Usize) : Result (Str × Str) :=
  let bs := Str.bytes s
  if Str.isCharBoundary bs mid.val then ok (Str.ofBytes (bs.take mid.val), Str.ofBytes (bs.drop mid.val))
  else fail .panic

/-- The bytes of `s` without the leading (and trailing, if `back`) whitespace. -/
@[expose] def Str.trimBytes (bs : List Nat) (front back : Bool) : List Nat :=
  let cs := (Str.toLeanString (Str.ofBytes bs)).toList
  let cs := if front then cs.dropWhile core.char.isWhitespace else cs
  let cs := if back then (cs.reverse.dropWhile core.char.isWhitespace).reverse else cs
  cs.flatMap utf8Encode

@[expose, rust_fun "core::str::{str}::trim"]
def core.str.Str.trim (s : Str) : Result Str := ok (Str.ofBytes (Str.trimBytes (Str.bytes s) true true))

@[expose, rust_fun "core::str::{str}::trim_start"]
def core.str.Str.trim_start (s : Str) : Result Str :=
  ok (Str.ofBytes (Str.trimBytes (Str.bytes s) true false))

/-! ## `FromStr` and `parse` -/

@[rust_trait "core::str::traits::FromStr"]
structure core.str.traits.FromStr (Self : Type _) (Self_Err : Type _) where
  from_str : Str → Result (core.result.Result Self Self_Err)

@[expose, rust_fun "core::str::{str}::parse"]
def core.str.Str.parse {F : Type _} {Clause0_Err : Type _}
    (traitsFromStrInst : core.str.traits.FromStr F Clause0_Err) (s : Str) :
    Result (core.result.Result F Clause0_Err) :=
  traitsFromStrInst.from_str s

/-! ## Patterns

Charon cannot translate the `Pattern` trait (it has a generic associated type), so the model is
not mapped to it: the trait impls for `char` and `&str` are provided below under the names Aeneas
uses for them, and a pattern is described by its UTF-8 encoding, which is all the needed methods
depend on (for valid UTF-8, the leftmost byte-occurrence of the encoding of a char or of a `str`
is the leftmost match). -/

structure core.str.pattern.Pattern (Self : Type _) where
  /-- The UTF-8 bytes that the pattern matches. -/
  encode : Self → List Nat

@[expose, reducible, rust_trait_impl "core::str::pattern::Pattern<char>"]
def Char.Insts.CoreStrPatternPattern : core.str.pattern.Pattern Char := { encode := utf8Encode }

@[expose, reducible, rust_trait_impl "core::str::pattern::Pattern<&'b str>"]
def SharedBStr.Insts.CoreStrPatternPattern : core.str.pattern.Pattern Str := { encode := Str.bytes }

/-- Leftmost occurrence of `needle` in `hay`. -/
@[expose] def listFind (hay needle : List Nat) : Option Nat :=
  let rec go (i : Nat) (hay : List Nat) : Option Nat :=
    if needle.isPrefixOf hay then some i
    else match hay with
      | [] => none
      | _ :: hay => go (i + 1) hay
  go 0 hay

/-- `str::match_indices`: the non-overlapping matches from left to right, as (byte start, byte
    length). An empty pattern matches at every char boundary. -/
@[expose] def core.str.pattern.Pattern.matchIndices {P : Type _}
    (inst : core.str.pattern.Pattern P) (haystack : Str) (p : P) : List (Nat × Nat) :=
  let needle := inst.encode p
  let hay := Str.bytes haystack
  if needle.isEmpty then
    ((List.range (hay.length + 1)).filter (Str.isCharBoundary hay)).map (fun i => (i, 0))
  else
    let n := needle.length
    let rec go (fuel i : Nat) (rest : List Nat) : List (Nat × Nat) :=
      match fuel with
      | 0 => []
      | fuel + 1 =>
        if needle.isPrefixOf rest then (i, n) :: go fuel (i + n) (rest.drop n)
        else match rest with
          | [] => []
          | _ :: rest => go fuel (i + 1) rest
    go (hay.length + 1) 0 hay

@[expose, rust_fun "core::str::{str}::starts_with"]
def core.str.Str.starts_with {P : Type _} (patternPatternInst : core.str.pattern.Pattern P)
    (s : Str) (p : P) : Result Bool :=
  ok ((patternPatternInst.encode p).isPrefixOf (Str.bytes s))

@[expose, rust_fun "core::str::{str}::find"]
def core.str.Str.find {P : Type _} (patternPatternInst : core.str.pattern.Pattern P)
    (s : Str) (p : P) : Result (Option Usize) :=
  ok ((listFind (Str.bytes s) (patternPatternInst.encode p)).map Usize.ofNatWrap)

@[expose, rust_fun "core::str::{str}::strip_prefix"]
def core.str.Str.strip_prefix {P : Type _} (patternPatternInst : core.str.pattern.Pattern P)
    (s : Str) (p : P) : Result (Option Str) :=
  let pre := patternPatternInst.encode p
  let bs := Str.bytes s
  ok (if pre.isPrefixOf bs then some (Str.ofBytes (bs.drop pre.length)) else none)

/-! ## Searchers -/

@[rust_type "core::str::pattern::SearchStep"]
inductive core.str.pattern.SearchStep where
  | Match : Usize → Usize → core.str.pattern.SearchStep
  | Reject : Usize → Usize → core.str.pattern.SearchStep
  | Done : core.str.pattern.SearchStep
deriving Inhabited, BEq

@[expose] def core.str.pattern.SearchStep.mk (isMatch : Bool) (a b : Nat) : core.str.pattern.SearchStep :=
  if isMatch then .Match (Usize.ofNatWrap a) (Usize.ofNatWrap b)
  else .Reject (Usize.ofNatWrap a) (Usize.ofNatWrap b)

@[rust_type "core::str::pattern::CharSearcher" (body := .opaque)]
structure core.str.pattern.CharSearcher where
  haystack : Str
  finger : Nat
  fingerBack : Nat
  needle : Char

@[expose, rust_fun "core::str::pattern::{core::str::pattern::Pattern<char>}::into_searcher"]
def Char.Insts.CoreStrPatternPattern.into_searcher (c : Char) (haystack : Str) :
    Result core.str.pattern.CharSearcher :=
  ok { haystack, finger := 0, fingerBack := (Str.bytes haystack).length, needle := c }

@[expose, rust_fun
  "core::str::pattern::{core::str::pattern::Searcher<'a, core::str::pattern::CharSearcher<'a>>}::haystack"]
def core.str.pattern.CharSearcher.Insts.CoreStrPatternSearcher.haystack
    (s : core.str.pattern.CharSearcher) : Result Str := ok s.haystack

@[expose, rust_fun
  "core::str::pattern::{core::str::pattern::Searcher<'a, core::str::pattern::CharSearcher<'a>>}::next"]
def core.str.pattern.CharSearcher.Insts.CoreStrPatternSearcher.next
    (s : core.str.pattern.CharSearcher) :
    Result (core.str.pattern.SearchStep × core.str.pattern.CharSearcher) :=
  let slice := ((Str.bytes s.haystack).drop s.finger).take (s.fingerBack - s.finger)
  match utf8First slice with
  | none => ok (.Done, s)
  | some (ch, w) =>
    let old := s.finger
    let s := { s with finger := old + w }
    ok (core.str.pattern.SearchStep.mk (ch == s.needle) old s.finger, s)

@[expose, rust_fun
  "core::str::pattern::{core::str::pattern::ReverseSearcher<'a, core::str::pattern::CharSearcher<'a>>}::next_back"]
def core.str.pattern.CharSearcher.Insts.CoreStrPatternReverseSearcher.next_back
    (s : core.str.pattern.CharSearcher) :
    Result (core.str.pattern.SearchStep × core.str.pattern.CharSearcher) :=
  let slice := ((Str.bytes s.haystack).drop s.finger).take (s.fingerBack - s.finger)
  match utf8Last slice with
  | none => ok (.Done, s)
  | some (ch, w) =>
    let old := s.fingerBack
    let s := { s with fingerBack := old - w }
    ok (core.str.pattern.SearchStep.mk (ch == s.needle) s.fingerBack old, s)

/-- `EmptyNeedle` state of `StrSearcher`. -/
structure core.str.pattern.EmptyNeedle where
  position : Nat
  «end» : Nat
  isMatchFw : Bool
  isMatchBw : Bool
  isFinished : Bool
deriving Inhabited

/-- `TwoWaySearcher` state (`memory = none` encodes Rust's `usize::MAX`: long period). -/
structure core.str.pattern.TwoWaySearcher where
  critPos : Nat
  critPosBack : Nat
  period : Nat
  byteset : Nat
  position : Nat
  «end» : Nat
  memory : Nat
  memoryBack : Nat
  longPeriod : Bool
deriving Inhabited

inductive core.str.pattern.StrSearcherImpl where
  | Empty (e : core.str.pattern.EmptyNeedle)
  | TwoWay (t : core.str.pattern.TwoWaySearcher)
deriving Inhabited

@[rust_type "core::str::pattern::StrSearcher" (body := .opaque)]
structure core.str.pattern.StrSearcher where
  haystack : Str
  needle : Str
  searcher : core.str.pattern.StrSearcherImpl

namespace core.str.pattern.TwoWaySearcher

/-- `TwoWaySearcher::maximal_suffix`. -/
@[expose] def maximalSuffix (arr : _root_.Array Nat) (orderGreater : Bool) : Nat × Nat :=
  let rec go (fuel left right offset period : Nat) : Nat × Nat :=
    match fuel with
    | 0 => (left, period)
    | fuel + 1 =>
      match arr[right + offset]? with
      | none => (left, period)
      | some a =>
        let b := arr[left + offset]!
        if (a < b && !orderGreater) || (a > b && orderGreater) then
          go fuel left (right + offset + 1) 0 (right + offset + 1 - left)
        else if a == b then
          if offset + 1 == period then go fuel left (right + offset + 1) 0 period
          else go fuel left right (offset + 1) period
        else go fuel right (right + 1) 0 1
  go (2 * arr.size + 2) 0 1 0 1

/-- `TwoWaySearcher::reverse_maximal_suffix`. -/
@[expose] def reverseMaximalSuffix (arr : _root_.Array Nat) (knownPeriod : Nat) (orderGreater : Bool) : Nat :=
  let n := arr.size
  let rec go (fuel left right offset period : Nat) : Nat :=
    match fuel with
    | 0 => left
    | fuel + 1 =>
      if right + offset < n then
        let a := arr[n - (1 + right + offset)]!
        let b := arr[n - (1 + left + offset)]!
        let (left, right, offset, period) :=
          if (a < b && !orderGreater) || (a > b && orderGreater) then
            (left, right + offset + 1, 0, right + offset + 1 - left)
          else if a == b then
            if offset + 1 == period then (left, right + offset + 1, 0, period)
            else (left, right, offset + 1, period)
          else (right, right + 1, 0, 1)
        if period == knownPeriod then left else go fuel left right offset period
      else left
  go (2 * n + 2) 0 1 0 1

@[expose] def mkByteset (bs : List Nat) : Nat :=
  bs.foldl (fun a b => a ||| 2 ^ (b % 64)) 0

@[expose] def byteContains (set b : Nat) : Bool := (set / 2 ^ (b % 64)) % 2 == 1

/-- `TwoWaySearcher::new`. -/
@[expose] def new (needle : _root_.Array Nat) (endPos : Nat) : core.str.pattern.TwoWaySearcher :=
  let (cf, pf) := maximalSuffix needle false
  let (ct, pt) := maximalSuffix needle true
  let (critPos, period) := if cf > ct then (cf, pf) else (ct, pt)
  let l := needle.toList
  if l.take critPos == (l.drop period).take critPos then
    let critPosBack := needle.size -
      max (reverseMaximalSuffix needle period false) (reverseMaximalSuffix needle period true)
    { critPos, critPosBack, period, byteset := mkByteset (l.take period), position := 0,
      «end» := endPos, memory := 0, memoryBack := needle.size, longPeriod := false }
  else
    { critPos, critPosBack := critPos, period := max critPos (needle.size - critPos) + 1,
      byteset := mkByteset l, position := 0, «end» := endPos, memory := 0, memoryBack := 0,
      longPeriod := true }

/-- `TwoWaySearcher::next::<RejectAndMatch>`: `(isMatch, a, b)`. -/
@[expose] def next (t : core.str.pattern.TwoWaySearcher) (hay needle : _root_.Array Nat) :
    (Bool × Nat × Nat) × core.str.pattern.TwoWaySearcher :=
  let oldPos := t.position
  let nlen := needle.size
  let long := t.longPeriod
  let rec search (fuel : Nat) (t : core.str.pattern.TwoWaySearcher) :
      (Bool × Nat × Nat) × core.str.pattern.TwoWaySearcher :=
    match fuel with
    | 0 => ((false, oldPos, hay.size), { t with position := hay.size })
    | fuel + 1 =>
      match hay[t.position + (nlen - 1)]? with
      | none => ((false, oldPos, hay.size), { t with position := hay.size })
      | some tail =>
        if oldPos != t.position then ((false, oldPos, t.position), t)
        else if !byteContains t.byteset tail then
          search fuel { t with position := t.position + nlen, memory := if long then t.memory else 0 }
        else
          let start := if long then t.critPos else max t.critPos t.memory
          -- right part
          match (List.range' start (nlen - start)).find? (fun i => needle[i]! != hay[t.position + i]!) with
          | some i =>
            search fuel { t with position := t.position + i - t.critPos + 1,
                                 memory := if long then t.memory else 0 }
          | none =>
            let start := if long then 0 else t.memory
            -- left part, from right to left
            match ((List.range' start (t.critPos - start)).reverse).find?
                (fun i => needle[i]! != hay[t.position + i]!) with
            | some _ =>
              search fuel { t with position := t.position + t.period,
                                   memory := if long then t.memory else nlen - t.period }
            | none =>
              let matchPos := t.position
              ((true, matchPos, matchPos + nlen),
                { t with position := t.position + nlen, memory := if long then t.memory else 0 })
  search (hay.size + 2) t

/-- `TwoWaySearcher::next_back::<RejectAndMatch>`: `(isMatch, a, b)`. -/
@[expose] def nextBack (t : core.str.pattern.TwoWaySearcher) (hay needle : _root_.Array Nat) :
    (Bool × Nat × Nat) × core.str.pattern.TwoWaySearcher :=
  let oldEnd := t.«end»
  let nlen := needle.size
  let long := t.longPeriod
  let rec search (fuel : Nat) (t : core.str.pattern.TwoWaySearcher) :
      (Bool × Nat × Nat) × core.str.pattern.TwoWaySearcher :=
    match fuel with
    | 0 => ((false, 0, oldEnd), { t with «end» := 0 })
    | fuel + 1 =>
      -- `haystack.get(self.end.wrapping_sub(needle.len()))`
      let front := if t.«end» < nlen then none else hay[t.«end» - nlen]?
      match front with
      | none => ((false, 0, oldEnd), { t with «end» := 0 })
      | some fb =>
        if oldEnd != t.«end» then ((false, t.«end», oldEnd), t)
        else if !byteContains t.byteset fb then
          search fuel { t with «end» := t.«end» - nlen, memoryBack := if long then t.memoryBack else nlen }
        else
          let crit := if long then t.critPosBack else min t.critPosBack t.memoryBack
          let base := t.«end» - nlen
          match ((List.range crit).reverse).find? (fun i => needle[i]! != hay[base + i]!) with
          | some i =>
            search fuel { t with «end» := t.«end» - (t.critPosBack - i),
                                 memoryBack := if long then t.memoryBack else nlen }
          | none =>
            let needleEnd := if long then nlen else t.memoryBack
            match (List.range' t.critPosBack (needleEnd - t.critPosBack)).find?
                (fun i => needle[i]! != hay[base + i]!) with
            | some _ =>
              search fuel { t with «end» := t.«end» - t.period,
                                   memoryBack := if long then t.memoryBack else t.period }
            | none =>
              let matchPos := base
              ((true, matchPos, matchPos + nlen),
                { t with «end» := base, memoryBack := if long then t.memoryBack else nlen })
  search (hay.size + 2) t

end core.str.pattern.TwoWaySearcher

@[expose, rust_fun "core::str::pattern::{core::str::pattern::Pattern<&'b str>}::into_searcher"]
def SharedBStr.Insts.CoreStrPatternPattern.into_searcher (needle haystack : Str) :
    Result core.str.pattern.StrSearcher :=
  let n := Str.bytes needle
  let hlen := (Str.bytes haystack).length
  if n.isEmpty then
    ok { haystack, needle, searcher := .Empty { position := 0, «end» := hlen, isMatchFw := true,
                                                isMatchBw := true, isFinished := false } }
  else
    ok { haystack, needle, searcher := .TwoWay (core.str.pattern.TwoWaySearcher.new n.toArray hlen) }

@[expose, rust_fun
  "core::str::pattern::{core::str::pattern::Searcher<'a, core::str::pattern::StrSearcher<'a, 'b>>}::haystack"]
def core.str.pattern.StrSearcher.Insts.CoreStrPatternSearcher.haystack
    (s : core.str.pattern.StrSearcher) : Result Str := ok s.haystack

@[expose, rust_fun
  "core::str::pattern::{core::str::pattern::Searcher<'a, core::str::pattern::StrSearcher<'a, 'b>>}::next"]
def core.str.pattern.StrSearcher.Insts.CoreStrPatternSearcher.next
    (s : core.str.pattern.StrSearcher) :
    Result (core.str.pattern.SearchStep × core.str.pattern.StrSearcher) :=
  let hay := Str.bytes s.haystack
  match s.searcher with
  | .Empty e =>
    if e.isFinished then ok (.Done, s) else
    let isMatch := e.isMatchFw
    let e := { e with isMatchFw := !e.isMatchFw }
    let pos := e.position
    if isMatch then ok (.Match (Usize.ofNatWrap pos) (Usize.ofNatWrap pos), { s with searcher := .Empty e })
    else match utf8First (hay.drop pos) with
      | none => ok (.Done, { s with searcher := .Empty { e with isFinished := true } })
      | some (_, w) =>
        ok (.Reject (Usize.ofNatWrap pos) (Usize.ofNatWrap (pos + w)),
            { s with searcher := .Empty { e with position := pos + w } })
  | .TwoWay t =>
    if t.position == hay.length then ok (.Done, s) else
    let ((isMatch, a, b), t) := t.next hay.toArray (Str.bytes s.needle).toArray
    if isMatch then ok (core.str.pattern.SearchStep.mk true a b, { s with searcher := .TwoWay t })
    else
      -- Round the end of the rejected range up to a char boundary.
      let b := (List.range' b (hay.length + 1 - b)).find? (Str.isCharBoundary hay) |>.getD hay.length
      let t := { t with position := max b t.position }
      ok (core.str.pattern.SearchStep.mk false a b, { s with searcher := .TwoWay t })

@[expose, rust_fun
  "core::str::pattern::{core::str::pattern::ReverseSearcher<'a, core::str::pattern::StrSearcher<'a, 'b>>}::next_back"]
def core.str.pattern.StrSearcher.Insts.CoreStrPatternReverseSearcher.next_back
    (s : core.str.pattern.StrSearcher) :
    Result (core.str.pattern.SearchStep × core.str.pattern.StrSearcher) :=
  let hay := Str.bytes s.haystack
  match s.searcher with
  | .Empty e =>
    if e.isFinished then ok (.Done, s) else
    let isMatch := e.isMatchBw
    let e := { e with isMatchBw := !e.isMatchBw }
    let en := e.«end»
    if isMatch then ok (.Match (Usize.ofNatWrap en) (Usize.ofNatWrap en), { s with searcher := .Empty e })
    else match utf8Last (hay.take en) with
      | none => ok (.Done, { s with searcher := .Empty { e with isFinished := true } })
      | some (_, w) =>
        ok (.Reject (Usize.ofNatWrap (en - w)) (Usize.ofNatWrap en),
            { s with searcher := .Empty { e with «end» := en - w } })
  | .TwoWay t =>
    if t.«end» == 0 then ok (.Done, s) else
    let ((isMatch, a, b), t) := t.nextBack hay.toArray (Str.bytes s.needle).toArray
    if isMatch then ok (core.str.pattern.SearchStep.mk true a b, { s with searcher := .TwoWay t })
    else
      -- Round the start of the rejected range down to a char boundary.
      let a := ((List.range (a + 1)).reverse.find? (Str.isCharBoundary hay)).getD 0
      let t := { t with «end» := min a t.«end» }
      ok (core.str.pattern.SearchStep.mk false a b, { s with searcher := .TwoWay t })

/-! ## Iterators -/

/-- `CharIndices`: the byte offset of the front and the remaining characters. -/
@[rust_type "core::str::iter::CharIndices" (body := .opaque)]
structure core.str.iter.CharIndices where
  frontOffset : Nat
  chars : List Char
deriving Inhabited

@[expose, rust_fun "core::str::{str}::char_indices"]
def core.str.Str.char_indices (s : Str) : Result core.str.iter.CharIndices :=
  ok { frontOffset := 0, chars := (Str.toLeanString s).toList }

@[expose, rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::CharIndices<'a>, (usize, char)>}::next"]
def core.str.iter.CharIndices.Insts.CoreIterTraitsIteratorIteratorPairUsizeChar.next
    (it : core.str.iter.CharIndices) :
    Result ((Option (Usize × Char)) × core.str.iter.CharIndices) :=
  match it.chars with
  | [] => ok (none, it)
  | c :: cs =>
    ok (some (Usize.ofNatWrap it.frontOffset, c),
        { frontOffset := it.frontOffset + c.utf8Size, chars := cs })

/-- `SplitWhitespace`: the remaining non-empty whitespace-separated pieces. -/
@[rust_type "core::str::iter::SplitWhitespace" (body := .opaque)]
structure core.str.iter.SplitWhitespace where
  words : List Str
deriving Inhabited

@[expose] def splitWhitespaceWords (cs : List Char) : List (List Char) :=
  let (cur, acc) := cs.foldl (fun (cur, acc) c =>
    if core.char.isWhitespace c then
      ([], if cur.isEmpty then acc else cur.reverse :: acc)
    else (c :: cur, acc)) ([], [])
  (if cur.isEmpty then acc else cur.reverse :: acc).reverse

@[expose, rust_fun "core::str::{str}::split_whitespace"]
def core.str.Str.split_whitespace (s : Str) : Result core.str.iter.SplitWhitespace :=
  let words := (splitWhitespaceWords (Str.toLeanString s).toList).map
    (fun w => Str.ofBytes (w.flatMap utf8Encode))
  ok { words }

@[expose, rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::SplitWhitespace<'a>, &'a str>}::next"]
def core.str.iter.SplitWhitespace.Insts.CoreIterTraitsIteratorIteratorSharedAStr.next
    (it : core.str.iter.SplitWhitespace) : Result ((Option Str) × core.str.iter.SplitWhitespace) :=
  match it.words with
  | [] => ok (none, it)
  | w :: ws => ok (some w, { words := ws })

/-- `last` is `next_back`. -/
@[expose, rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::SplitWhitespace<'a>, &'a str>}::last"]
def core.str.iter.SplitWhitespace.Insts.CoreIterTraitsIteratorIteratorSharedAStr.last
    (it : core.str.iter.SplitWhitespace) : Result (Option Str) :=
  ok it.words.getLast?

/-- `Filter<Split<..>, ..>::size_hint` is `(0, upper)` and `Split` has the default `(0, None)`. -/
@[expose, rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::SplitWhitespace<'a>, &'a str>}::size_hint"]
def core.str.iter.SplitWhitespace.Insts.CoreIterTraitsIteratorIteratorSharedAStr.size_hint
    (_ : core.str.iter.SplitWhitespace) : Result (Usize × (Option Usize)) :=
  ok (Usize.ofNatWrap 0, none)

/-! ## Indexing (`SliceIndex<str>` for `Range<usize>` and `RangeFrom<usize>`) -/

/-- The byte range `[a, b)` of `s` if it is a valid `str` slice. -/
@[expose] def Str.sub? (s : Str) (a b : Nat) : Option Str :=
  let bs := Str.bytes s
  if a ≤ b && Str.isCharBoundary bs a && Str.isCharBoundary bs b then
    some (Str.ofBytes ((bs.drop a).take (b - a)))
  else none

/-- `s` with the byte range `[a, b)` replaced by `r`. -/
@[expose] def Str.replaceSub (s : Str) (a b : Nat) (r : Str) : Str :=
  let bs := Str.bytes s
  Str.ofBytes (bs.take a ++ Str.bytes r ++ bs.drop b)

@[expose, rust_fun "core::str::traits::{core::ops::index::Index<str, @I, @Clause0_Output>}::index"]
def Str.Insts.CoreOpsIndexIndex.index {I : Type _} {Clause0_Output : Type _}
    (sliceindexSliceIndexIStrClause0_OutputInst : core.slice.index.SliceIndex I Str Clause0_Output)
    (s : Str) (i : I) : Result Clause0_Output :=
  sliceindexSliceIndexIStrClause0_OutputInst.index i s

section
variable (r : core.ops.range.Range Usize) (s : Str)

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get : Result (Option Str) :=
  ok (Str.sub? s r.start.val r.«end».val)

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::index"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index : Result Str :=
  match Str.sub? s r.start.val r.«end».val with
  | some x => ok x
  | none => fail .panic

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get_mut"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_mut :
    Result ((Option Str) × (Option Str → Str)) :=
  ok (Str.sub? s r.start.val r.«end».val,
      fun o => match o with
        | some x => Str.replaceSub s r.start.val r.«end».val x
        | none => s)

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::index_mut"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index_mut :
    Result (Str × (Str → Str)) :=
  match Str.sub? s r.start.val r.«end».val with
  | some x => ok (x, Str.replaceSub s r.start.val r.«end».val)
  | none => fail .panic

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get_unchecked"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked
    (p : ConstRawPtr Str) : Result (ConstRawPtr Str) :=
  match Str.sub? p.v r.start.val r.«end».val with
  | some x => ok { v := x }
  | none => fail .undef

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get_unchecked_mut"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked_mut
    (p : MutRawPtr Str) : Result (MutRawPtr Str) :=
  match Str.sub? p.v r.start.val r.«end».val with
  | some x => ok { v := x }
  | none => fail .undef

end

section
variable (r : core.ops.range.RangeFrom Usize) (s : Str)

@[expose] def Str.fromLen (s : Str) : Nat := (Str.bytes s).length

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get : Result (Option Str) :=
  ok (Str.sub? s r.start.val (Str.fromLen s))

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::index"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.index : Result Str :=
  match Str.sub? s r.start.val (Str.fromLen s) with
  | some x => ok x
  | none => fail .panic

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get_mut"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_mut :
    Result ((Option Str) × (Option Str → Str)) :=
  ok (Str.sub? s r.start.val (Str.fromLen s),
      fun o => match o with
        | some x => Str.replaceSub s r.start.val (Str.fromLen s) x
        | none => s)

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::index_mut"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.index_mut :
    Result (Str × (Str → Str)) :=
  match Str.sub? s r.start.val (Str.fromLen s) with
  | some x => ok (x, Str.replaceSub s r.start.val (Str.fromLen s))
  | none => fail .panic

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get_unchecked"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked
    (p : ConstRawPtr Str) : Result (ConstRawPtr Str) :=
  match Str.sub? p.v r.start.val (Str.fromLen p.v) with
  | some x => ok { v := x }
  | none => fail .undef

@[expose, rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get_unchecked_mut"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked_mut
    (p : MutRawPtr Str) : Result (MutRawPtr Str) :=
  match Str.sub? p.v r.start.val (Str.fromLen p.v) with
  | some x => ok { v := x }
  | none => fail .undef

end

/-! ## `char` methods -/

@[expose, rust_fun "core::char::methods::{char}::to_digit"]
def core.char.methods.Char.to_digit (c : Char) (radix : U32) : Result (Option U32) :=
  -- Rust 1.96: `to_digit` panics if `radix` is not in `2..=36`.
  if radix.val < 2 || 36 < radix.val then fail .panic else
  let x := c.toNat
  let d := if 48 ≤ x && x ≤ 57 then some (x - 48)
    else if 97 ≤ x && x ≤ 122 then some (x - 87)
    else if 65 ≤ x && x ≤ 90 then some (x - 55) else none
  ok (match d with
    | some d => if d < radix.val then some ⟨BitVec.ofNat _ d⟩ else none
    | none => none)

@[expose, rust_fun "core::char::methods::{char}::is_digit"]
def core.char.methods.Char.is_digit (c : Char) (radix : U32) : Result Bool := do
  let d ← core.char.methods.Char.to_digit c radix
  ok d.isSome

@[expose, rust_fun "core::char::methods::{char}::is_ascii_alphabetic"]
def core.char.methods.Char.is_ascii_alphabetic (c : Char) : Result Bool :=
  let x := c.toNat
  ok ((65 ≤ x && x ≤ 90) || (97 ≤ x && x ≤ 122))

end Aeneas.Std
