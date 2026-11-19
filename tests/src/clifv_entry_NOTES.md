# clifv-entry: `clifv_extract_entry::compile_aarch64` (WIP, paused)

Status: compile_aarch64 does NOT translate yet. The two source changes on this
branch compile (`make build-dev`), but they are not covered by tests and have
not been checked with `make extract-tests`.

## Root causes found

1. **Original failure: `InterpBorrows.ml:2112` (sanity `borrows = []` in
   `destructure_abs`).** The `'static` region abstractions of the
   `Context::compile` / `map_err` / `branch` calls hold loan projectors over
   `Result<&'r CompiledCodeBase<Final>, CompileError<'r>>` with nested
   children (`borrows=[...]` on `AProjLoans`, `loans=[...]` on `AProjBorrows`).
   These children appear once `'r` (the `&mut ctx` region) ends, because of the
   `'static` borrows hidden inside `CompiledCode`. They are destructured either
   at a branch join (`eval_switch_with_join`) or, after fix A below, at the
   break join of the isa-flags `for` loop (`loop_join_break_ctxs` ->
   `destructure_new_abs`, `InterpBorrows.ml:2119`).
   - Trace: the `-log InterpStatements,InterpJoin` run, context printed before
     the failure.
2. **Charon's control-flow reconstruction nests the whole function tail inside
   the loops.** The `None` arm of the shared-flags `for` loop contains the
   isa-flags loop, and the isa-flags loop's `None` arm contains everything else
   (`Flags::new`, `new_with_flags`, `compile`, the `Artifact` build), ending
   with `break 17` to the final `return`. So every loop's fixed point and
   break-join carries the whole compile state, including the abstractions
   from (1).
3. **Settings-loop shape** (`for s in flags { b.set(..).map_err(..)?; }`).
   Minimal repros are in `/data/clifv-extract/work/ie/repros/`: `r1151.rs`,
   `rst.rs`, and `ent.rs`, a mini version of the entry. `ent2.rs` is `ent.rs`
   without the loop, and it translates. Failures in sequence:
   - `InterpReduceCollapse.ml:1193`: markers left in an abstraction
     continuation. The cause is the join of "iter alive" with "iter dead":
     `storage_dead(iter)` in the `?` branch was not removed because a
     `conditional_drop` sat between it and the escape.
   - Fix A then exposed `InterpMatchCtxs.ml:1721`: a mut loan on `iter` at
     `continue`, because the `StorageDead(_8)` before the lowered
     `continue 1` had been dropped.
   - Fix B then exposed `ValuesUtils.ml:43`, which is not investigated yet.
     `ent.rs` still fails at 1193.

## Changes on this branch

- **A. `PrePasses.ml` (`split_storage_dead_before_escape`).** The trailing
  `StorageDead`s removed before a rewritten escape may now be interleaved with
  `Drop`s, which are no-ops under `Config.drop_as_no_op`. The drops are kept.
  - Sound: `StorageDead` only ends borrows. Keeping a local alive longer is
    checked by the interpreter.
- **B. `lower_loop_exits`.** The `StorageDead`s removed before a lowered
  `continue d` (d >= 1) are re-emitted in the dispatch branch, before the
  `continue`. The context at the continue must match the loop entry, where
  those locals are dead.
  - Faithful: it runs the same statements, with no effects in between.
- **C. `InterpBorrows.destructure_abs`.** The children of loan and borrow
  projectors (and of ended projectors) are flattened into the abstraction when
  the abstraction's regions appear only below shared borrows in the projected
  type (`shared_only_in`). Otherwise it fails as before (`cassert`).
  - Same argument as the existing nested-shared-borrow flattening: the meaning
    of a projector doesn't depend on its position, and shared borrows give
    back nothing.
  - Not yet run on the entry. The run was interrupted by the pause.

## Next steps

1. Rerun `AENEAS_ONLY=clifv_extract_entry::compile_aarch64` with C to see
   whether 2112/2119 are gone.
2. Planned generic pre-pass `hoist_loop_exit_branches`, to run before
   `ret_to_carrier`:
   - **Rule.** For a loop L, find a branch E inside L's body (possibly inside
     block loops that never continue) that always escapes, has no `continue`
     to L or to any loop between E and L, and whose break and continue targets
     are all outside L (or are returns). Replace E with
     `x := K; break (k-1)`, where k is the number of loops from E up to and
     including L. Right after L, insert
     `switch x { K => E', _ => {} }`, where E' is E with every escape depth
     reduced by k.
   - **Soundness.** Nothing executes between the break and the dispatch, so the
     semantics are exact.
   - **Effect.** This un-nests the compile tail from both settings loops, so
     their fixed points and break joins only carry the iterator state.
3. Fix `ValuesUtils.ml:43` for `r1151.rs` and `rst.rs`.
4. Then add the tests:
   - `clifv_entry_settings_loop.rs`: the `r1151`/`ent` shapes.
   - `clifv_entry_static_nested_proj.rs`: the compile `Result<&T, Err<'a>>`
     with hidden `'static` data.

   Each needs `#[verify::test]` asserts, run natively with rustc 1.96, and a
   Lean build; then run `make extract-tests -k`.
