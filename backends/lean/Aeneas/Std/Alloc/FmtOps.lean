/- Formatting in `alloc`/`std`: `alloc::fmt::format`, `ToString`, `String` as `Display`/`Debug`,
and the `Debug` impls of `BTreeMap`/`HashMap` (`Formatter::debug_map`). -/
module
public import Aeneas.Std.Alloc.StringOps
public import Aeneas.Std.Alloc.Collections.BTreeMap
public import Aeneas.Std.Std.Collections
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

open Result

/-- `format(args)`: renders the arguments; Rust panics if a formatting implementation returns
    an error. -/
@[expose, rust_fun "alloc::fmt::format"]
def alloc.fmt.format (args : core.fmt.Arguments) : Result String := do
  let r ← core.fmt.Arguments.render args
  match r with
  | .Ok s => ok s
  | .Err _ => fail .panic

/-- `ToString` blanket impl: `Display::fmt` into a fresh `String` with default options; Rust
    panics if `fmt` returns an error. -/
@[expose, rust_fun "alloc::string::{alloc::string::ToString<@T>}::to_string"]
def alloc.string.ToString.Blanket.to_string {T : Type _} (displayInst : core.fmt.Display T)
    (x : T) : Result String := do
  let r ← core.fmt.fmtToString displayInst.fmt x
  match r with
  | .Ok s => ok s
  | .Err _ => fail .panic

/-- `<str as Display>::fmt`: `Formatter::pad`. -/
@[expose, rust_fun "alloc::string::{core::fmt::Display<alloc::string::String>}::fmt"]
def alloc.string.String.Insts.CoreFmtDisplay.fmt (s : String) (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  core.fmt.Formatter.pad f s

/-- `<str as Debug>::fmt`: quoted, `escape_debug`-escaped. -/
@[expose, rust_fun "alloc::string::{core::fmt::Debug<alloc::string::String>}::fmt"]
def alloc.string.String.Insts.CoreFmtDebug.fmt (s : String) (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  core.fmt.Formatter.debug_str f s

namespace FmtModel

/-- `PadAdapter`: insert four spaces at the start of every line (state `on_newline` starts
    `true`). -/
@[expose] def padLines (s : String) : String :=
  let (out, _) := s.foldl (fun (acc : String × Bool) c =>
    let (out, onNewline) := acc
    let out := if onNewline then out ++ "    " else out
    (out.push c, c == '\n')) ("", true)
  out

/-- Run `fmt` on a formatter with the same options as `f` and an empty buffer, returning the
    output (`Formatter::wrap_buf`). -/
@[expose] def renderWith {X : Type u} (f : core.fmt.Formatter)
    (fmt : X → core.fmt.Formatter → Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter))
    (x : X) : Result ((core.result.Result String core.fmt.Error)) := do
  let (r, g) ← fmt x { f with buf := "" }
  match r with
  | .Ok _ => ok (.Ok g.buf)
  | .Err e => ok (.Err e)

/-- Sequence two formatting steps, stopping at the first error. -/
@[expose] def seq
    (r : Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter))
    (k : core.fmt.Formatter →
      Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) := do
  let (r, f) ← r
  match r with
  | .Err e => ok (.Err e, f)
  | .Ok _ => k f

/-- The entries and closing brace of `DebugMap` (`entry` for each, then `finish`). In pretty
    (`{:#?}`) mode, each `key: value,\n` goes through a `PadAdapter`. -/
@[expose] def debugMapEntries {K : Type u} {V : Type v} (debugK : core.fmt.Debug K)
    (debugV : core.fmt.Debug V) (pretty hasFields : Bool) (f : core.fmt.Formatter) :
    List (K × V) → Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  | [] => core.fmt.Formatter.write_string f "}"
  | (k, v) :: rest =>
    if pretty then
      seq (if hasFields then ok (.Ok (), f) else core.fmt.Formatter.write_string f "\n")
        fun f => do
          let rk ← renderWith f debugK.fmt k
          match rk with
          | .Err e => ok (.Err e, f)
          | .Ok ks => do
            let rv ← renderWith f debugV.fmt v
            match rv with
            | .Err e => ok (.Err e, f)
            | .Ok vs =>
              seq (core.fmt.Formatter.write_string f (padLines (ks ++ ": " ++ vs ++ ",\n")))
                fun f => debugMapEntries debugK debugV pretty true f rest
    else
      seq (if hasFields then core.fmt.Formatter.write_string f ", " else ok (.Ok (), f))
        fun f => seq (debugK.fmt k f)
        fun f => seq (core.fmt.Formatter.write_string f ": ")
        fun f => seq (debugV.fmt v f)
        fun f => debugMapEntries debugK debugV pretty true f rest

/-- `f.debug_map().entries(entries).finish()`. -/
@[expose] def debugMap {K : Type u} {V : Type v} (debugK : core.fmt.Debug K)
    (debugV : core.fmt.Debug V) (entries : List (K × V)) (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  seq (core.fmt.Formatter.write_string f "{")
    fun f => debugMapEntries debugK debugV (core.fmt.Formatter.alternate f) false f entries

end FmtModel

@[expose, rust_fun
  "alloc::collections::btree::map::{core::fmt::Debug<alloc::collections::btree::map::BTreeMap<@K, @V, @A>>}::fmt"]
def alloc.collections.btree.map.BTreeMap.Insts.CoreFmtDebug.fmt {K : Type _} {V : Type _}
    {A : Type _} (debugK : core.fmt.Debug K) (debugV : core.fmt.Debug V)
    (_allocInst : core.alloc.AllocatorClone A) (m : alloc.collections.btree.map.BTreeMap K V A)
    (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  FmtModel.debugMap debugK debugV m.entries f

/-- Entries in the model's iteration order (see `Std/Collections.lean`). -/
@[expose, rust_fun
  "std::collections::hash::map::{core::fmt::Debug<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::fmt"]
def std.collections.hash.map.HashMap.Insts.CoreFmtDebug.fmt {K : Type _} {V : Type _} {S : Type _}
    {A : Type _} (debugK : core.fmt.Debug K) (debugV : core.fmt.Debug V)
    (m : std.collections.hash.map.HashMap K V S A) (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  FmtModel.debugMap debugK debugV m.entries f

end Aeneas.Std
