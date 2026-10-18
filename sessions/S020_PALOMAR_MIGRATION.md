# S020 — Lean toolchain migration to v4.35.0 (Palomar minimum)

**Date:** 2026-10-18
**Type:** Migration session (owner-authorised). No mathematics or Lean source changed.
**Base revision:** `a801196`/`15c8d56` line (`main` after S019 and the docs commits).
**Migration proof commit:** `b114ccd295440b1b85414beecc946de3991ca64e`. The closeout commit follows it.

## Scope
- **As installed:** the owner asked for "a Palomar migration session … ahead of S020", run immediately. The S020 prompt covered the toolchain, a module-system port and a Palomar submission package.
- **Narrowed mid-session** by the owner: "you don't need to build the palomar package - just make sure the lean version is on track". So this session migrated only the toolchain. The module-system port and the submission package were **not** done; they are recorded as open in `docs/ROADMAP.md`.

## Changes
- `formal/lean-toolchain`: `leanprover/lean4:v4.34.1` → `leanprover/lean4:v4.35.0`. This is at least the Palomar minimum `v4.35.0-rc2` (`PalomarSubmission/toolchains.json`, read 2026-10-18).
- The local elan default is now v4.35.0.
- `theorems/frozen/MIGRATION-S020/`: migration record, clean-clone build log, axiom log, axiom diff against v4.34.1, and perft log.
- `theorems/frozen/EC-T0001…EC-T0006/v2.md`: one per frozen theorem, re-anchoring it on v4.35.0. v1 is unchanged.
- `docs/PROOF_PROTOCOL.md`: a new "Toolchain migration" rule. `theorems/README.md`, `formal/README.md`, `README.md` and `docs/ROADMAP.md` (Palomar status) are updated.
- `NEXT_SESSION.md`: S021 (EC-C008 Lean, part 1) is installed. It was previously planned as S020.

## Findings
- The library builds on v4.35.0 **with no source edits**.
- All `#check`/`#print` output is byte-identical to v4.34.1.
- The axioms of every frozen main declaration are unchanged: `[propext, Classical.choice, Quot.sound]`.
- 37 auxiliary lemmas now also depend on `Classical.choice`. This comes from Lean core changes and stays within the permitted three.
- Perft: all 11 checks OK.

## Checks actually run (local)
- Scratch clone on v4.35.0: `lake build` OK in 54 s; `AxiomCheck` diffed against the v4.34.1 working tree; `Checks/Perft.lean` OK.
- **Fresh GitHub clone at `b114ccd`, no `.lake`:**
  - `lake build`: exit 0, 17 jobs;
  - `AxiomCheck`: exit 0, 101 reports, all within the standard three, no `sorryAx`/`ofReduceBool`, identical to the scratch run;
  - forbidden-token grep: 0 matches.
- `python scripts/validate_ledger.py` and the Python tests: see the session ledger row.
- CI: not observed.

## Ledger effect
None: the ledger has one row per ID and is unchanged. 6 frozen theorems, now with v2 manifests on v4.35.0.

## Installed next session
See `NEXT_SESSION.md` at this commit (S021: Lean formalisation of EC-C008, part 1).
