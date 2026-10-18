# Toolchain migration S020: Lean v4.34.1 → v4.35.0

**Date:** 2026-10-18. **Migration proof commit:** `b114ccd295440b1b85414beecc946de3991ca64e`. **Owner authorisation:** S020 instruction (Palomar compatibility: `PalomarSubmission/toolchains.json` minimum `v4.35.0-rc2`, checked 2026-10-18).

## What changed
- `formal/lean-toolchain`: `leanprover/lean4:v4.34.1` → `leanprover/lean4:v4.35.0` (Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`).
- **No Lean source file changed.** `git diff 60b03e9 b114ccd -- 'formal/*.lean' 'formal/**/*.lean'` is empty. Every module hash in the v1 manifests is therefore unchanged.
- No module-system port was made (owner scope: "just make sure the lean version is on track"). Palomar's `module`-header requirement remains open; see `docs/ROADMAP.md`.

## Verification (local, Windows, elan)
- Fresh `git clone` from GitHub at `b114ccd295440b1b85414beecc946de3991ca64e`, with no `.lake`. `cd formal && lake build`: exit 0, 17 jobs. Log: [lake_build.log](lake_build.log).
- `lake env lean AxiomCheck.lean`: exit 0. There are 101 reports, all ⊆ `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` and no `Lean.ofReduceBool`. Log: [axioms.log](axioms.log).
- **Statements unchanged:** every `#check` and `#print` line in `AxiomCheck.lean` is byte-identical between v4.34.1 and v4.35.0.
- **Axioms of every frozen main declaration unchanged:** `[propext, Classical.choice, Quot.sound]` for all of
  - `KK.dead_of_admissible`;
  - `KBK.dead_of_LKBK`;
  - `Rules.arisen_KK_dead` and `Rules.arisen_KBK_dead`;
  - `Rules.dead_of_legal_into_KK`, `Rules.dead_of_legal_into_KBK` and `Rules.dead_of_legal_into_KNK`;
  - `Rules.arisen_KNK_dead`;
  - `Rules.krk_dead_of_forced_capture`.
- **One difference:** 37 auxiliary declarations that previously reported `[propext, Quot.sound]` or `[propext]` now also report `Classical.choice`. This is a change in Lean core library lemmas between versions, not in this repository. All three axioms remain within the permitted standard set. Full diff: [axioms_diff_v4.34.1_to_v4.35.0.txt](axioms_diff_v4.34.1_to_v4.35.0.txt).
- Perft cross-check (`lake env lean Checks/Perft.lean`): all 11 values OK. Log: [perft.log](perft.log).
- Word-bounded forbidden-token grep over `formal/**/*.lean`: no matches.

## Record-keeping
- v1 manifests and ledger rows are unchanged. They remain valid records reproducible at their cited commits on v4.34.1.
- Each frozen theorem gets a `v2.md` that re-anchors it on v4.35.0 at `b114ccd`.
- The ledger schema has one row per ID, so the ledger is unchanged; `theorems/README.md` names the current version.
