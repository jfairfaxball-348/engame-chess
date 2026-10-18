# S012 — Lean formalisation of EC-C003 (K+N vs K) over the rules kernel (Gate F)

**Date:** 2026-10-18
**Type:** Theorem session (Lean).
**Base revision:** `2ce3fb4` (`main`, S011 closeout).
**Proof-source commit:** `3adcebbb4ae643a62c8bf18b478bf70da774dbf8` (branch `claude/s012-knk-lean`). The closeout commit follows it and does not cite its own SHA.

## Changes
- `formal/EndgameChess/Rules/KNK.lean` (new, imports `Rules.Outcome`): `knkBoard`, `IsKNK`; attack/check characterisation; N0 `kings_apart_of_legal`, `strong_not_inCheck`; N1 `knightGeom_iff`, `knight_not_orth`, `ne_of_knight_adj`; N2 `escape_square`, `weak_has_move`; N3 `step_closed`; N4 `reach_cases`, `not_mated_KNK`; main `dead_of_legal_into_KNK`, `arisen_KNK_dead`, `knk_drawn_by_rule`, `initial_not_KNK`; non-vacuity `knight_check_example`, `knk_stalemate_example`, `knight_capture_example`.
- `formal/EndgameChess.lean` (import), `formal/AxiomCheck.lean` (18 new `#print axioms`, 3 `#check`).
- `audits/EC-C003_KNK_LEAN.md` (new). Status files: `research/CANDIDATES.md`, `README.md`, `docs/ROADMAP.md`, `formal/README.md`.
- `NEXT_SESSION.md`: S013 (freeze as EC-T0005) installed.
- No frozen module edited.

## Findings, separated
- **Proved (Lean, kernel):** every K+N vs K position (either orientation, any flags) produced by any kernel-legal move from any position is `DeadK`; every arisen one is `DeadK`; under `Rule5_2_2` it is an immediate draw.
- **Proved non-vacuity (decide):** a legal knight check into K+N vs K; a K+N vs K stalemate; a legal knight capture into K vs K.
- **Computationally tested:** unchanged from S011 (Python diagnostic; not re-run, no Python changed).
- **Conjectured:** none.
- **Deviation from plan:** N4 uses "reachable from a legally-entered K vs K position" and EC-T0003, instead of re-proving K vs K closure. Statement unchanged.

## Checks actually run (all local, Lean 4.34.1)
- `lake env lean EndgameChess/Rules/KNK.lean`: no errors, no warnings.
- `lake build` (working tree): `Build completed successfully (16 jobs)`.
- Fresh `git clone` of the local repository at `3adcebbb4ae643a62c8bf18b478bf70da774dbf8`, empty `.lake`: `lake build` succeeded (16 jobs, 39.5 s); `lake env lean AxiomCheck.lean` exit 0, 92 reports all ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`/`ofReduceBool` (logs in the Lean audit).
- Forbidden-token grep on `KNK.lean`: none.
- `python scripts/validate_ledger.py`: `LEDGER VALID: 4 frozen theorem(s) (structure only)`.
- CI: not observed.

## Status and ledger effect
EC-C003: `LOCAL_VERIFIED → FORMAL_VERIFIED`. `theorems/LEDGER.csv` unchanged. Frozen theorems: **4**.

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S013: freeze EC-C003 (K+N vs K, over the rules kernel) as EC-T0005, Gate Z
>
> **Owner instruction:** Execute this S013 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C003 is `FORMAL_VERIFIED` (S012). Do not treat this prompt as evidence that it is frozen.
>
> ## Context
> - Frozen: EC-T0001–EC-T0004. EC-T0003/0004 (S010) are the template for a kernel-level freeze: `theorems/frozen/EC-T0004/v1.md` with `lake_build.log` and `axioms.log` beside it.
> - EC-C003: proof [proofs/EC-C003_KNK.md](proofs/EC-C003_KNK.md), audits [audits/EC-C003_KNK.md](audits/EC-C003_KNK.md) and [audits/EC-C003_KNK_LEAN.md](audits/EC-C003_KNK_LEAN.md). Lean module `formal/EndgameChess/Rules/KNK.lean`; **proof-source commit `3adcebbb4ae643a62c8bf18b478bf70da774dbf8`** (S012).
> - **Local Lean is the primary check** (owner instruction): elan default toolchain `leanprover/lean4:v4.34.1` (commit `5045d00…`). Push as `jfairfaxball-348` (repo-local git config routes github.com credentials to Git Credential Manager).
>
> ## Objective
> Freeze EC-C003 as **EC-T0005** under `docs/PROOF_PROTOCOL.md` Gate Z. No change to mathematics or Lean source.
>
> ## Required work
> 1. **Fresh-clone verification** of `3adcebb…`: `git clone` from GitHub into a scratch directory, check out the proof commit, no `.lake`; `cd formal && lake build` and `lake env lean AxiomCheck.lean`. Save both outputs verbatim as `theorems/frozen/EC-T0005/lake_build.log` and `axioms.log`. Confirm every axiom report ⊆ `[propext, Classical.choice, Quot.sound]`, and no `sorryAx` / `Lean.ofReduceBool`.
> 2. **Manifest** `theorems/frozen/EC-T0005/v1.md`, following EC-T0004's structure:
>    - statement in prose (no-possible-mate, either orientation, any legal arrival from any material, any flags; arisen form; `Rule5_2_2` corollary) and in Lean (verbatim `#check` of `dead_of_legal_into_KNK`, `arisen_KNK_dead`, `knk_drawn_by_rule`, and `#print Rule5_2_2`);
>    - dependencies: frozen EC-T0003 (`dead_of_legal_into_KK`) for the capture branch, and the kernel modules frozen with EC-T0003/0004;
>    - evidence: SHA-256 of `Rules/KNK.lean` and of every kernel module it imports at the proof commit, plus the bridge `docs/RULES_KERNEL.md` hash (as in S010);
>    - note: unlike EC-T0001–0004 there is **no bespoke predecessor**, so there are no G1/G2 gaps to close; the S011 prompt's reversed colour claim and its correction (proof §0);
>    - trust boundary: A1, open human review of the kernel bridge, the 5.2.2 reading, same-session audits, trusted base.
> 3. **Ledger:** one new `FROZEN` row `EC-T0005` in `theorems/LEDGER.csv` citing `3adcebbb4ae643a62c8bf18b478bf70da774dbf8`, lean_declaration `EndgameChess.Rules.arisen_KNK_dead`, file `formal/EndgameChess/Rules/KNK.lean`. Earlier rows byte-identical (check with `cmp` against the previous file); keep LF line endings. `python scripts/validate_ledger.py` must report 5 frozen theorems.
> 4. Update `theorems/README.md` (count 5), `research/CANDIDATES.md` (EC-C003 → frozen as EC-T0005), `README.md`, `docs/ROADMAP.md`, `formal/README.md`.
>
> ## Next research candidate (install as S014 at closeout)
> Propose S014 as a Gate P + Gate L session for the next roadmap rung. Read `docs/ROADMAP.md`; the natural next candidate is **K+B vs K+B with same-coloured bishops** (all bishops on one square colour: dead; a known classical case under FIDE 5.2.2), stated over the kernel, with a precise statement of which positions are covered (including bishops of both sides, any number on one colour if the roadmap prefers the general form) and a diagnostic plus mutation test. If the roadmap names a different next rung, follow the roadmap and say why.
>
> ## Closeout
> `sessions/S013_FREEZE_EC-T0005.md` and a `sessions/SESSION_LEDGER.md` row: changes; checks actually run (fresh clone, local); base SHA and proof SHA; ledger effect (**+1 → EC-T0005**, 5 frozen). Install S014 in full. Commit, push, merge to `main`.
