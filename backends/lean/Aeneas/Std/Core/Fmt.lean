module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Result
public import Aeneas.Std.Array.Array
public import Aeneas.Std.StringDef
public section

/-!
# `core::fmt`

An executable model of Rust 1.96's formatting machinery which produces exactly the strings
`core` produces.

* A `Formatter` is the formatting options (`FormattingOptions`: `flags`, `width`, `precision`,
  with Rust's bit layout for `flags`) together with the output written so far (`buf`). Rust's
  formatter writes into a `&mut dyn fmt::Write`; here the sink is an append-only `String`
  (all the sinks of the modeled code are strings, and they never fail).
* `rt::Argument` closes over the value and the `fmt` method of the trait selected by
  `format_args!` (or is a `usize` count for dynamic widths/precisions).
* `Arguments` is either a static string (`Arguments::from_str`) or a 1.96 byte-encoded
  template with its arguments, interpreted by `core.fmt.write` exactly as `core::fmt::write`.
* The `Debug` builders (`debug_struct`, `debug_tuple`, lists, maps) implement the `{:#?}`
  pretty-printing through `PadAdapter`, applied to the output of each field.

Known deviation: for non-ASCII characters, `Debug` escaping uses an approximation of Rust's
Unicode `is_printable`/`Grapheme_Extend` tables (C1 controls, U+00AD and combining diacritical
marks U+0300..U+036F are escaped, everything else is printed verbatim). ASCII is exact.
-/

namespace Aeneas.Std

@[reducible, expose, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

/-! ## `str` ↔ `String` -/

/-- The Lean string of a Rust `str` (Rust `str`s are always valid UTF-8). -/
@[expose] def Str.toLeanString (s : Str) : String :=
  match String.fromUTF8? (ByteArray.mk ((Slice.val (α := U8) s).map (fun b => UInt8.ofNat b.val)).toArray) with
  | some str => str
  | none => ""

/-- The Rust `str` of a Lean string. -/
@[expose] def Str.ofLeanString (s : String) : Str :=
  let l : List U8 := s.toUTF8.toList.map (fun b => ⟨BitVec.ofNat _ b.toNat⟩)
  if h : l.length ≤ Usize.max then Slice.from l h
  else Slice.from (l.take Usize.max) (by simp)

/-! ## Formatter -/

/-- `Formatter`: Rust's `FormattingOptions` plus the output buffer. -/
@[rust_type "core::fmt::Formatter" (body := .opaque)]
structure core.fmt.Formatter where
  /-- The output written so far. -/
  buf : String
  /-- `FormattingOptions::flags`: fill (bits 0-20), `+` (21), `-` (22), `#` (23), `0` (24),
      `x?` (25), `X?` (26), width present (27), precision present (28), align (29-30, 3 = unset). -/
  flags : Nat := 0x60000020
  width : Nat := 0
  precision : Nat := 0
deriving Inhabited

/-- `Formatter::new(output, FormattingOptions::new())` with an empty output. -/
@[expose] def core.fmt.Formatter.new : core.fmt.Formatter := { buf := "" }

/-- The result type of all the `fmt` methods. -/
abbrev core.fmt.FmtResult := Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

namespace core.fmt.Formatter

@[expose] def flag (f : core.fmt.Formatter) (bit : Nat) : Bool := (f.flags / 2^bit) % 2 == 1
@[expose] def fill (f : core.fmt.Formatter) : Char := Char.ofNat (f.flags % 2^21)
@[expose] def signPlus (f : core.fmt.Formatter) : Bool := f.flag 21
@[expose] def alternate (f : core.fmt.Formatter) : Bool := f.flag 23
@[expose] def signAwareZeroPad (f : core.fmt.Formatter) : Bool := f.flag 24
@[expose] def debugLowerHex (f : core.fmt.Formatter) : Bool := f.flag 25
@[expose] def debugUpperHex (f : core.fmt.Formatter) : Bool := f.flag 26
@[expose] def hasWidth (f : core.fmt.Formatter) : Bool := f.flag 27
@[expose] def getPrecision (f : core.fmt.Formatter) : Option Nat :=
  if f.flag 28 then some f.precision else none
/-- `0`: left, `1`: right, `2`: center, `3`: unset. -/
@[expose] def alignBits (f : core.fmt.Formatter) : Nat := (f.flags / 2^29) % 4

/-- A formatter with the same options and an empty buffer (used to render a sub-value). -/
@[expose] def fresh (f : core.fmt.Formatter) : core.fmt.Formatter := { f with buf := "" }

/-- Append to the output (writing to a `String` never fails). -/
@[expose] def push (f : core.fmt.Formatter) (s : String) : core.fmt.Formatter :=
  { f with buf := f.buf ++ s }

/-- Write a Lean string: `self.buf.write_str(s)`. -/
@[expose] def write_string (f : core.fmt.Formatter) (s : String) : core.fmt.FmtResult :=
  .ok (.Ok (), f.push s)

/-- `Formatter::padding` followed by the write of `s` and of the post padding.
    `default` is the alignment used when none is set (`0` left, `1` right). -/
@[expose] def padded (f : core.fmt.Formatter) (padding : Nat) (default : Nat) (s : String) :
    core.fmt.Formatter :=
  let align := if f.alignBits == 3 then default else f.alignBits
  let left := match align with
    | 0 => 0
    | 1 => padding
    | _ => padding / 2
  let fillStr (n : Nat) := String.ofList (List.replicate n f.fill)
  f.push (fillStr left ++ s ++ fillStr (padding - left))

/-- `Formatter::pad`: precision truncation, then width/fill/alignment (left by default). -/
@[expose] def pad (f : core.fmt.Formatter) (s : String) : core.fmt.FmtResult :=
  if !f.flag 27 && !f.flag 28 then .ok (.Ok (), f.push s) else
  let (s, count) := match f.getPrecision with
    | some p => let cs := s.toList.take p; (String.ofList cs, cs.length)
    | none => (s, s.length)
  if count < f.width then .ok (.Ok (), f.padded (f.width - count) 0 s)
  else .ok (.Ok (), f.push s)

/-- `Formatter::pad_integral`. -/
@[expose] def pad_integral (f : core.fmt.Formatter) (isNonnegative : Bool) (pfx : String)
    (digits : String) : core.fmt.FmtResult :=
  let sign : String := if !isNonnegative then "-" else if f.signPlus then "+" else ""
  let pfx := if f.alternate then pfx else ""
  let width := digits.length + sign.length + pfx.length
  if width ≥ f.width then .ok (.Ok (), f.push (sign ++ pfx ++ digits))
  else if f.signAwareZeroPad then
    let f' := { f with flags := (f.flags / 2^21) * 2^21 % 2^29 + 2^29 + '0'.toNat }
    let f' := (f'.push (sign ++ pfx)).padded (f.width - width) 1 digits
    .ok (.Ok (), { f' with flags := f.flags })
  else .ok (.Ok (), f.padded (f.width - width) 1 (sign ++ pfx ++ digits))

/-- Run `fmtFn` on a fresh formatter with the same options and return what it wrote. -/
@[expose] def render (f : core.fmt.Formatter)
    (fmtFn : core.fmt.Formatter → core.fmt.FmtResult) :
    Result (core.result.Result Unit core.fmt.Error × String) := do
  let (r, f') ← fmtFn f.fresh
  .ok (r, f'.buf)

end core.fmt.Formatter

/-- `PadAdapter` with a fresh state (`on_newline = true`): indent every line by 4 spaces. -/
@[expose] def core.fmt.padAdapter (s : String) : String :=
  let rec go (onNewline : Bool) (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: cs =>
      let acc := if onNewline then ' ' :: ' ' :: ' ' :: ' ' :: acc else acc
      go (c == '\n') cs (c :: acc)
  String.ofList (go true s.toList [])

/-- Format a value through a `PadAdapter` wrapping the formatter (`{:#?}` builders), followed by
    `suffix` written through the same adapter. -/
@[expose] def core.fmt.Formatter.writePadded (f : core.fmt.Formatter)
    (pfx : String) (fmtFn : core.fmt.Formatter → core.fmt.FmtResult) (suffix : String) :
    core.fmt.FmtResult := do
  let (r, out) ← f.render (fun g => do
    let g := g.push pfx
    let (r, g) ← fmtFn g
    match r with
    | .Ok () => .ok (.Ok (), g.push suffix)
    | .Err e => .ok (.Err e, g))
  .ok (r, f.push (core.fmt.padAdapter out))

/-- Sequence formatting steps, stopping at the first error (Rust's `?`). -/
@[expose] def core.fmt.Formatter.seq (f : core.fmt.Formatter)
    (steps : List (core.fmt.Formatter → core.fmt.FmtResult)) : core.fmt.FmtResult :=
  match steps with
  | [] => .ok (.Ok (), f)
  | s :: steps => do
    let (r, f) ← s f
    match r with
    | .Ok () => core.fmt.Formatter.seq f steps
    | .Err e => .ok (.Err e, f)

/-! ## `Debug` builders -/

/-- `DebugStruct`: `name`, then the fields, then `finish()`. -/
@[expose] def core.fmt.Formatter.debugStruct (f : core.fmt.Formatter) (name : String)
    (fields : List (String × (core.fmt.Formatter → core.fmt.FmtResult))) : core.fmt.FmtResult :=
  let pretty := f.alternate
  let fieldStep (i : Nat) (nv : String × (core.fmt.Formatter → core.fmt.FmtResult)) :
      core.fmt.Formatter → core.fmt.FmtResult := fun g =>
    if pretty then
      let g := if i == 0 then g.push " {\n" else g
      g.writePadded (nv.1 ++ ": ") nv.2 ",\n"
    else
      let g := g.push ((if i == 0 then " { " else ", ") ++ nv.1 ++ ": ")
      nv.2 g
  let finish : List (core.fmt.Formatter → core.fmt.FmtResult) :=
    if fields.isEmpty then [] else [fun g => g.write_string (if pretty then "}" else " }")]
  f.seq ([fun g => g.write_string name] ++ (fields.mapIdx fieldStep) ++ finish)

/-- `DebugTuple`: `name`, then the fields, then `finish()`. -/
@[expose] def core.fmt.Formatter.debugTuple (f : core.fmt.Formatter) (name : String)
    (fields : List (core.fmt.Formatter → core.fmt.FmtResult)) : core.fmt.FmtResult :=
  let pretty := f.alternate
  let fieldStep (i : Nat) (v : core.fmt.Formatter → core.fmt.FmtResult) :
      core.fmt.Formatter → core.fmt.FmtResult := fun g =>
    if pretty then
      let g := if i == 0 then g.push "(\n" else g
      g.writePadded "" v ",\n"
    else v (g.push (if i == 0 then "(" else ", "))
  let finish : List (core.fmt.Formatter → core.fmt.FmtResult) :=
    if fields.isEmpty then []
    else [fun g => g.write_string
      ((if fields.length == 1 && name.isEmpty && !pretty then "," else "") ++ ")")]
  f.seq ([fun g => g.write_string name] ++ (fields.mapIdx fieldStep) ++ finish)

/-- `DebugList` (`open = "["`, `close = "]"`) and `DebugSet` (`"{"`, `"}"`). -/
@[expose] def core.fmt.Formatter.debugInner (f : core.fmt.Formatter) (opn cls : String)
    (entries : List (core.fmt.Formatter → core.fmt.FmtResult)) : core.fmt.FmtResult :=
  let pretty := f.alternate
  let entryStep (i : Nat) (v : core.fmt.Formatter → core.fmt.FmtResult) :
      core.fmt.Formatter → core.fmt.FmtResult := fun g =>
    if pretty then
      let g := if i == 0 then g.push "\n" else g
      g.writePadded "" v ",\n"
    else v (if i == 0 then g else g.push ", ")
  f.seq ([fun g => g.write_string opn] ++ (entries.mapIdx entryStep) ++
    [fun g => g.write_string cls])

@[expose] def core.fmt.Formatter.debugList (f : core.fmt.Formatter)
    (entries : List (core.fmt.Formatter → core.fmt.FmtResult)) : core.fmt.FmtResult :=
  f.debugInner "[" "]" entries

/-- `DebugMap`: `{k: v, ...}`; in pretty mode each `k: v,\n` goes through one `PadAdapter`. -/
@[expose] def core.fmt.Formatter.debugMap (f : core.fmt.Formatter)
    (entries : List ((core.fmt.Formatter → core.fmt.FmtResult) ×
      (core.fmt.Formatter → core.fmt.FmtResult))) : core.fmt.FmtResult :=
  let pretty := f.alternate
  let entryStep (i : Nat) (kv : (core.fmt.Formatter → core.fmt.FmtResult) ×
      (core.fmt.Formatter → core.fmt.FmtResult)) :
      core.fmt.Formatter → core.fmt.FmtResult := fun g =>
    if pretty then
      let g := if i == 0 then g.push "\n" else g
      g.writePadded "" (fun h => h.seq [kv.1, fun h => h.write_string ": ", kv.2]) ",\n"
    else
      (if i == 0 then g else g.push ", ").seq [kv.1, fun h => h.write_string ": ", kv.2]
  f.seq ([fun g => g.write_string "{"] ++ (entries.mapIdx entryStep) ++
    [fun g => g.write_string "}"])

/-! ## Traits -/

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type u) where
  fmt : T → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::Display"]
structure core.fmt.Display (Self : Type _) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::LowerHex"]
structure core.fmt.LowerHex (Self : Type _) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

/-! ## `Arguments` -/

/-- `core::fmt::rt::Argument`: a value with its formatting function, or a count
    (`Argument::from_usize`, for dynamic widths and precisions). -/
@[rust_type "core::fmt::rt::Argument" (body := .opaque)]
inductive core.fmt.rt.Argument where
  | placeholder (fmt : core.fmt.Formatter → core.fmt.FmtResult)
  | count (n : Nat)

instance : Inhabited core.fmt.rt.Argument := ⟨.count 0⟩

/-- `core::fmt::Arguments`: a static string, or a byte-encoded template and its arguments. -/
@[rust_type "core::fmt::Arguments" (body := .opaque)]
inductive core.fmt.Arguments where
  | str (s : String)
  | template (t : List Nat) (args : List core.fmt.rt.Argument)

instance : Inhabited core.fmt.Arguments := ⟨.str ""⟩

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str"]
def core.fmt.Arguments.from_str (s : Str) : Result core.fmt.Arguments := .ok (.str s.toLeanString)

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::new"]
def core.fmt.Arguments.new {N : Std.Usize} {M : Std.Usize}
  (template : Std.Array Std.U8 N) (args : Std.Array core.fmt.rt.Argument M) :
  Result core.fmt.Arguments :=
  .ok (.template (template.val.map (·.val)) args.val)

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_debug"]
def core.fmt.rt.Argument.new_debug
  {T : Type _} (DebugInst : core.fmt.Debug T) (x : T) : Result core.fmt.rt.Argument :=
  .ok (.placeholder (DebugInst.fmt x))

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_display"]
def core.fmt.rt.Argument.new_display
  {T : Type _} (DisplayInst : core.fmt.Display T) (x : T) : Result core.fmt.rt.Argument :=
  .ok (.placeholder (DisplayInst.fmt x))

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_lower_hex"]
def core.fmt.rt.Argument.new_lower_hex
  {T : Type _} (LowerHexInst : core.fmt.LowerHex T) (x : T) : Result core.fmt.rt.Argument :=
  .ok (.placeholder (LowerHexInst.fmt x))

/-- Panics if the count does not fit in a `u16`. -/
@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::from_usize"]
def core.fmt.rt.Argument.from_usize (x : Std.Usize) : Result core.fmt.rt.Argument :=
  if x.val > 65535 then .fail .panic else .ok (.count x.val)

/-- Little-endian number made of the first `n` bytes. -/
@[expose] def core.fmt.leNum (bs : List Nat) (n : Nat) : Nat :=
  (bs.take n).foldr (fun b acc => b + 256 * acc) 0

/-- The UTF-8 string of a list of bytes. -/
@[expose] def core.fmt.bytesToString (bs : List Nat) : String :=
  match String.fromUTF8? (ByteArray.mk (bs.map UInt8.ofNat).toArray) with
  | some s => s
  | none => ""

/-- The interpreter of `core::fmt::write`, generic in the output `σ`: `emitStr` writes a literal
    piece, `emitArg` formats an argument with a new `Formatter` (`flags`, `width`, `precision`)
    writing to the same output. Arguments are used in template order, as in Rust. The template is
    assumed valid (as Rust does); an invalid one fails. -/
@[expose] def core.fmt.interpTemplate {σ : Type _}
    (emitStr : σ → String → Result (core.result.Result Unit core.fmt.Error × σ))
    (emitArg : σ → (core.fmt.Formatter → core.fmt.FmtResult) → Nat → Nat → Nat →
      Result (core.result.Result Unit core.fmt.Error × σ))
    (args : List core.fmt.rt.Argument) :
    Nat → σ → List Nat → Nat → Result (core.result.Result Unit core.fmt.Error × σ)
  | 0, _, _, _ => .fail .undef
  | _ + 1, _, [], _ => .fail .undef
  | fuel + 1, out, n :: t, argIdx =>
    let next (r : core.result.Result Unit core.fmt.Error × σ) (t : List Nat) (argIdx : Nat) :=
      match r with
      | (.Ok (), out) => core.fmt.interpTemplate emitStr emitArg args fuel out t argIdx
      | (.Err e, out) => .ok (.Err e, out)
    if n == 0 then .ok (.Ok (), out)
    else if n < 0x80 then do
      let r ← emitStr out (core.fmt.bytesToString (t.take n))
      next r (t.drop n) argIdx
    else if n == 0x80 then do
      let len := core.fmt.leNum t 2
      let t := t.drop 2
      let r ← emitStr out (core.fmt.bytesToString (t.take len))
      next r (t.drop len) argIdx
    else if n < 0xC0 then .fail .undef
    else do
      let (flags, t) := if n % 2 == 1 then (core.fmt.leNum t 4, t.drop 4) else (0x60000020, t)
      let (width, t) := if (n / 2) % 2 == 1 then (core.fmt.leNum t 2, t.drop 2) else (0, t)
      let (precision, t) := if (n / 4) % 2 == 1 then (core.fmt.leNum t 2, t.drop 2) else (0, t)
      let (argIdx, t) := if (n / 8) % 2 == 1 then (core.fmt.leNum t 2, t.drop 2) else (argIdx, t)
      let count (i : Nat) : Result Nat :=
        match args[i]? with
        | some (.count c) => .ok c
        | _ => .fail .undef
      let width ← if (n / 16) % 2 == 1 then count width else .ok width
      let precision ← if (n / 32) % 2 == 1 then count precision else .ok precision
      match args[argIdx]? with
      | some (.placeholder fmt) => do
        let r ← emitArg out fmt flags width precision
        next r t (argIdx + 1)
      | _ => .fail .undef

/-- `core::fmt::write(output, args)` for a `String` output. -/
@[expose] def core.fmt.write (out : String) (a : core.fmt.Arguments) :
    Result (core.result.Result Unit core.fmt.Error × String) :=
  match a with
  | .str s => .ok (.Ok (), out ++ s)
  | .template t args =>
    core.fmt.interpTemplate (fun out s => .ok (.Ok (), out ++ s))
      (fun out fmt flags width precision => do
        let (r, f) ← fmt { buf := out, flags, width, precision }
        .ok (r, f.buf))
      args (t.length + 1) out t 0

/-- Render `Arguments` to a string (`alloc::fmt::format`, `ToString` for `Arguments`, ...). -/
@[expose] def core.fmt.Arguments.render (a : core.fmt.Arguments) :
    Result (core.result.Result String core.fmt.Error) := do
  let (r, s) ← core.fmt.write "" a
  match r with
  | .Ok () => .ok (.Ok s)
  | .Err e => .ok (.Err e)

/-- Render a value with a `fmt` method and default options (`ToString::to_string`). -/
@[expose] def core.fmt.fmtToString {T : Type _}
    (fmt : T → core.fmt.Formatter → core.fmt.FmtResult) (x : T) :
    Result (core.result.Result String core.fmt.Error) := do
  let (r, f) ← fmt x core.fmt.Formatter.new
  match r with
  | .Ok () => .ok (.Ok f.buf)
  | .Err e => .ok (.Err e)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"]
def core.fmt.Formatter.write_str (fmt : core.fmt.Formatter) (s : Str) : core.fmt.FmtResult :=
  .ok (.Ok (), fmt.push s.toLeanString)

/-- `Formatter::write_fmt`: writes the arguments to the underlying output (the options of
    `fmt` are not used). -/
@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"]
def core.fmt.Formatter.write_fmt (fmt : core.fmt.Formatter) (a : core.fmt.Arguments) :
    core.fmt.FmtResult := do
  let (r, buf) ← core.fmt.write fmt.buf a
  .ok (r, { fmt with buf })

@[expose, rust_fun "core::fmt::{core::fmt::Display<core::fmt::Arguments<'0>>}::fmt"]
def core.fmt.Arguments.Insts.CoreFmtDisplay.fmt (a : core.fmt.Arguments)
    (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  core.fmt.Formatter.write_fmt f a

/-! ## `fmt::Write` -/

/-- `core::fmt::write` to a generic `fmt::Write`: literal pieces are written with `write_str`;
    each placeholder is rendered and its output written with one `write_str` (equivalent to
    Rust's sequence of writes for sinks whose `write_str` appends, such as `String`). -/
@[expose] def core.fmt.writeTo {Self : Type _}
    (write_str : Self → Str → Result ((core.result.Result Unit core.fmt.Error) × Self))
    (s : Self) (a : core.fmt.Arguments) :
    Result ((core.result.Result Unit core.fmt.Error) × Self) :=
  let piece (s : Self) (str : String) := write_str s (Str.ofLeanString str)
  match a with
  | .str str => piece s str
  | .template t args =>
    core.fmt.interpTemplate piece
      (fun s fmt flags width precision => do
        let (r, f) ← fmt { buf := "", flags, width, precision }
        let (r', s) ← if f.buf.isEmpty then .ok (.Ok (), s) else piece s f.buf
        match r with
        | .Ok () => .ok (r', s)
        | .Err e => .ok (.Err e, s))
      args (t.length + 1) s t 0

@[rust_trait "core::fmt::Write"]
structure core.fmt.Write (Self : Type _) where
  write_str : Self → Str → Result ((core.result.Result Unit core.fmt.Error) × Self)
  write_char : Self → Char → Result ((core.result.Result Unit core.fmt.Error) × Self) :=
    fun s c => write_str s (Str.ofLeanString c.toString)
  write_fmt : Self → core.fmt.Arguments → Result ((core.result.Result Unit core.fmt.Error) × Self) :=
    fun s a => core.fmt.writeTo write_str s a

/-- `Write::write_char`: `self.write_str(c.encode_utf8(&mut [0; 4]))`. -/
@[expose, trait_default, rust_fun "core::fmt::Write::write_char"]
def core.fmt.Write.write_char.default {Self : Type _} (WriteInst : core.fmt.Write Self)
    (s : Self) (c : Char) : Result ((core.result.Result Unit core.fmt.Error) × Self) :=
  WriteInst.write_str s (Str.ofLeanString c.toString)

/-- `Write::write_fmt`: `core::fmt::write(self, args)`. -/
@[expose, trait_default, rust_fun "core::fmt::Write::write_fmt"]
def core.fmt.Write.write_fmt.default {Self : Type _} (WriteInst : core.fmt.Write Self)
    (s : Self) (a : core.fmt.Arguments) : Result ((core.result.Result Unit core.fmt.Error) × Self) :=
  core.fmt.writeTo WriteInst.write_str s a

/-! ## Character escapes (`char::escape_debug_ext`) -/

/-- Approximation of `core::unicode::printable::is_printable` (exact on ASCII). -/
@[expose] def core.fmt.isPrintable (c : Char) : Bool :=
  let x := c.toNat
  if x < 0x20 then false
  else if x < 0x7f then true
  else if x ≤ 0x9f then false
  else x != 0xad

/-- Approximation of `Grapheme_Extend` (combining diacritical marks). -/
@[expose] def core.fmt.isGraphemeExtended (c : Char) : Bool :=
  0x300 ≤ c.toNat && c.toNat ≤ 0x36f

@[expose] def core.fmt.hexLower (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

/-- `char::escape_debug_ext`. -/
@[expose] def core.fmt.escapeDebug (c : Char) (graphemeExtended singleQuote doubleQuote : Bool) :
    String :=
  if c == '\x00' then "\\0"
  else if c == '\t' then "\\t"
  else if c == '\r' then "\\r"
  else if c == '\n' then "\\n"
  else if c == '\\' then "\\\\"
  else if c == '"' && doubleQuote then "\\\""
  else if c == '\'' && singleQuote then "\\'"
  else if graphemeExtended && core.fmt.isGraphemeExtended c then
    "\\u{" ++ core.fmt.hexLower c.toNat ++ "}"
  else if core.fmt.isPrintable c then c.toString
  else "\\u{" ++ core.fmt.hexLower c.toNat ++ "}"

/-- `<str as Debug>::fmt` on a Lean string. -/
@[expose] def core.fmt.Formatter.debug_str (f : core.fmt.Formatter) (s : String) :
    core.fmt.FmtResult :=
  .ok (.Ok (), f.push ("\"" ++ String.join (s.toList.map (core.fmt.escapeDebug · true false true))
    ++ "\""))

/-! ## `Debug`/`Display` impls of `core::fmt` -/

@[expose, rust_fun "core::fmt::{core::fmt::Debug<str>}::fmt"]
def Str.Insts.CoreFmtDebug.fmt (s : Str) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  f.debug_str s.toLeanString

@[expose, rust_fun "core::fmt::{core::fmt::Display<str>}::fmt"]
def Str.Insts.CoreFmtDisplay.fmt (s : Str) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  f.pad s.toLeanString

@[expose, rust_fun "core::fmt::{core::fmt::Debug<char>}::fmt"]
def Char.Insts.CoreFmtDebug.fmt (c : Char) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  .ok (.Ok (), f.push ("'" ++ core.fmt.escapeDebug c true true false ++ "'"))

@[expose, rust_fun "core::fmt::{core::fmt::Display<bool>}::fmt"]
def Bool.Insts.CoreFmtDisplay.fmt (b : Bool) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  f.pad (if b then "true" else "false")

@[expose, rust_fun "core::fmt::{core::fmt::Debug<bool>}::fmt"]
def core.fmt.DebugBool.fmt (b : Bool) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  f.pad (if b then "true" else "false")

@[expose, rust_fun "core::fmt::{core::fmt::Debug<()>}::fmt"]
def core.fmt.DebugUnit.fmt (_ : Unit) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  f.pad "()"

@[expose, rust_fun "core::fmt::{core::fmt::Debug<!>}::fmt"]
def Never.Insts.CoreFmtDebug.fmt (x : Never) (_ : core.fmt.Formatter) : core.fmt.FmtResult :=
  nomatch x

@[expose, rust_fun "core::fmt::{core::fmt::Debug<core::fmt::Error>}::fmt"]
def core.fmt.Error.Insts.CoreFmtDebug.fmt (_ : core.fmt.Error) (f : core.fmt.Formatter) :
    core.fmt.FmtResult :=
  f.write_string "Error"

@[expose, rust_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"]
def core.fmt.DebugShared.fmt {T : Type _} (DebugInst : core.fmt.Debug T) (x : T)
  (fmt : core.fmt.Formatter) : core.fmt.FmtResult :=
  DebugInst.fmt x fmt

@[expose, rust_fun "core::fmt::{core::fmt::Debug<&'0 mut @T>}::fmt"]
def Mut0T.Insts.CoreFmtDebug.fmt {T : Type _} (DebugInst : core.fmt.Debug T) (x : T)
  (fmt : core.fmt.Formatter) : core.fmt.FmtResult :=
  DebugInst.fmt x fmt

@[expose, rust_fun "core::fmt::{core::fmt::Display<&'0 @T>}::fmt"]
def Shared0T.Insts.CoreFmtDisplay.fmt {T : Type _} (DisplayInst : core.fmt.Display T) (x : T)
  (fmt : core.fmt.Formatter) : core.fmt.FmtResult :=
  DisplayInst.fmt x fmt

@[expose, rust_fun "core::fmt::{core::fmt::Debug<(@U, @T)>}::fmt"]
def Pair.Insts.CoreFmtDebug.fmt {U : Type _} {T : Type _} (DebugInst : core.fmt.Debug U)
    (DebugInst1 : core.fmt.Debug T) (x : U × T) (f : core.fmt.Formatter) : core.fmt.FmtResult :=
  f.debugTuple "" [DebugInst.fmt x.1, DebugInst1.fmt x.2]

@[expose, rust_fun "core::fmt::{core::fmt::Debug<(@V, @U, @T)>}::fmt"]
def TupleVUT.Insts.CoreFmtDebug.fmt {V : Type _} {U : Type _} {T : Type _}
    (DebugInst : core.fmt.Debug V) (DebugInst1 : core.fmt.Debug U)
    (DebugInst2 : core.fmt.Debug T) (x : V × U × T) (f : core.fmt.Formatter) :
    core.fmt.FmtResult :=
  f.debugTuple "" [DebugInst.fmt x.1, DebugInst1.fmt x.2.1, DebugInst2.fmt x.2.2]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field1_finish"]
def core.fmt.Formatter.debug_struct_field1_finish
  (fmt : core.fmt.Formatter) (name : Str) (n1 : Str) (v1 : Dyn (fun dyn => core.fmt.Debug dyn)) :
  core.fmt.FmtResult :=
  fmt.debugStruct name.toLeanString [(n1.toLeanString, v1.inst.fmt v1.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish"]
def core.fmt.Formatter.debug_struct_field2_finish (fmt : core.fmt.Formatter) (name : Str)
  (n1 : Str) (v1 : Dyn (fun dyn => core.fmt.Debug dyn))
  (n2 : Str) (v2 : Dyn (fun dyn => core.fmt.Debug dyn)) :
  core.fmt.FmtResult :=
  fmt.debugStruct name.toLeanString
    [(n1.toLeanString, v1.inst.fmt v1.value), (n2.toLeanString, v2.inst.fmt v2.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field3_finish"]
def core.fmt.Formatter.debug_struct_field3_finish (fmt : core.fmt.Formatter) (name : Str) :
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  core.fmt.FmtResult :=
  fun n1 v1 n2 v2 n3 v3 =>
  fmt.debugStruct name.toLeanString
    [(n1.toLeanString, v1.inst.fmt v1.value), (n2.toLeanString, v2.inst.fmt v2.value),
     (n3.toLeanString, v3.inst.fmt v3.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field4_finish"]
def core.fmt.Formatter.debug_struct_field4_finish (fmt : core.fmt.Formatter) (name : Str) :
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  core.fmt.FmtResult :=
  fun n1 v1 n2 v2 n3 v3 n4 v4 =>
  fmt.debugStruct name.toLeanString
    [(n1.toLeanString, v1.inst.fmt v1.value), (n2.toLeanString, v2.inst.fmt v2.value),
     (n3.toLeanString, v3.inst.fmt v3.value), (n4.toLeanString, v4.inst.fmt v4.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field5_finish"]
def core.fmt.Formatter.debug_struct_field5_finish (fmt : core.fmt.Formatter) (name : Str) :
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  core.fmt.FmtResult :=
  fun n1 v1 n2 v2 n3 v3 n4 v4 n5 v5 =>
  fmt.debugStruct name.toLeanString
    [(n1.toLeanString, v1.inst.fmt v1.value), (n2.toLeanString, v2.inst.fmt v2.value),
     (n3.toLeanString, v3.inst.fmt v3.value), (n4.toLeanString, v4.inst.fmt v4.value),
     (n5.toLeanString, v5.inst.fmt v5.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field1_finish"]
def core.fmt.Formatter.debug_tuple_field1_finish :
  core.fmt.Formatter → Str → Dyn (fun dyn => core.fmt.Debug dyn) → core.fmt.FmtResult :=
  fun fmt name v1 => fmt.debugTuple name.toLeanString [v1.inst.fmt v1.value]

@[expose, reducible, rust_trait_impl "core::fmt::Debug<&'0 @T>"]
def core.fmt.DebugShared {T : Type _} (DebugInst : core.fmt.Debug T) :
  core.fmt.Debug T := {
  fmt := core.fmt.DebugShared.fmt DebugInst
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<()>"]
def core.fmt.DebugUnit : core.fmt.Debug Unit := {
  fmt := core.fmt.DebugUnit.fmt
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<bool>"]
def core.fmt.DebugBool : core.fmt.Debug Bool := {
  fmt := core.fmt.DebugBool.fmt
}

/-! ## `Result::unwrap`/`expect` (they need `Debug` for the panic message) -/

@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type _}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

@[step]
theorem core.result.Result.unwrap.step_spec
    {T E : Type _} (inst : core.fmt.Debug E)
    (r : core.result.Result T E)
    (h : ∃ v, r = core.result.Result.Ok v) :
    core.result.Result.unwrap inst r
    ⦃ (result : T) => r = core.result.Result.Ok result ⦄ := by
  match r, h with
  | .Ok v, ⟨_, rfl⟩ =>
    simp [core.result.Result.unwrap, WP.spec_ok]

/-- `Result::<&mut T, E>::unwrap`: the unwrapped value, and the backward function which gives back
    the result holding the value written through the borrow. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap<&'a mut @T, @E>"]
def core.result.Result.unwrap.mut {T E : Type _}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result (T × (T → core.result.Result T E)) :=
  match e with
  | .Ok x => .ok (x, fun x => .Ok x)
  | .Err _ => .fail .panic

@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::expect"]
def core.result.Result.expect {T : Type _} {E : Type _} (_DebugInst : core.fmt.Debug E)
  (r : core.result.Result T E) (_ : Str) : Std.Result T :=
  match r with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

end Aeneas.Std
