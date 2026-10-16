# S001 — K-vs-K dead-position proof (Gate L)

**Date:** 2026-10-16
**Type:** Theorem session (local mathematics only).
**Base revision:** `848524bd7f9fe575eaf3e4f165d0dba176bf4210` (S000 bootstrap). The S001 commit is the child of this revision on branch `claude/exciting-thompson-onvc27`; its own SHA is not self-cited.

## Changes
- `docs/FOUNDATIONS.md` — repaired: side to move bound into the step relation; KK legal moves derived from FIDE 3.1–3.9 (no stipulated "not attacked" clause, which the 2023 Art. 3.8.1 lacks); explicit `Arisen`, `Checkmate`, `Stalemate`, `Reach`, `Dead`; counterfactual move graph explained.
- `proofs/EC-C001_KK.md` — new self-contained proof: verbatim FIDE 2023 quotations; lemmas L0 (arisen ⇒ admissible), L1 (attack ⇔ `d∞=1`), L2 (no check), L3a (legal moves = `LegalKK`), L3 (step closure), L4 (path induction), L5 (no reachable mate), L6 (quantifier); theorem; 5.2.2 immediate-draw corollary; remark R1 (no stalemate; a legal move always exists).
- `audits/EC-C001_KK.md` — new hostile audit: 17 attempted falsifications, repairs, diagnostic output, residual assumptions.
- `scripts/kk_diagnostic.py`, `tests/test_kk_diagnostic.py` — exhaustive self-contained enumeration (no tablebase), labelled supplementary.
- `research/CANDIDATES.md` — EC-C001 → `LOCAL_VERIFIED`. `research/KK_DRAFT.md` marked superseded (content kept). README, ROADMAP, session ledger updated.
- `NEXT_SESSION.md` — S002 (Lean 4 formalisation) installed.

## Findings, separated
- **Proved (paper, Gate L):** every admissible KK configuration is dead; every game-arisen KK configuration is admissible; hence FIDE 5.2.2 immediate draw. Also R1: no admissible KK configuration is stalemate.
- **Computationally tested (supplement only):** all 8192 configurations — 7224 admissible, 0 checks, 0 checkmates, 0 stalemates, 0 closure/turn violations over 44 352 legal moves; all 840 adjacent configurations are double check.
- **Conjectured:** none new.
- **Blocked / not done:** Lean formalisation (not started); independent second-reader audit (audit was same-session).
- **Repairs to S000:** StepKK lacked side-to-move binding; draft mis-attributed the non-adjacency rule to Art. 3.8.

## Checks actually run
- `python3 scripts/kk_diagnostic.py` → consistent (output in audit §3).
- `python3 -m unittest discover -s tests -v` → 9 tests, OK.
- `python3 scripts/validate_ledger.py` → `LEDGER VALID: 0 frozen theorem(s) (structure only)`.
- FIDE page retrieved via curl (SHA-256 `c5b1692a…476f`); WebFetch returned 503.
- **Not run:** any Lean build (no Lean project exists); remote CI (no result observed in this session).

## Status and ledger effect
EC-C001: `PROPOSED → LOCAL_VERIFIED`. `theorems/LEDGER.csv` unchanged (header only). Frozen theorems: **0**.

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S002: Faithful Lean 4 formalisation of EC-C001 (K vs K dead position)
>
> **Owner instruction:** Execute this S002 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. EC-C001 is `LOCAL_VERIFIED` only; do not treat this prompt as evidence that any Lean proof exists or compiles.
>
> ## Objective
> Create a pinned, reproducible Lean 4 project under `formal/` that states and proves, **faithfully to** `proofs/EC-C001_KK.md` and `docs/FOUNDATIONS.md`, that every admissible two-king configuration is dead (no finite legal path reaches a checkmate of either colour), and that every two-king configuration produced by a legal king move is admissible. Reach Gate F (`FORMAL_VERIFIED`) only if every Gate F check in `docs/PROOF_PROTOCOL.md` actually passes. **Do not freeze; keep `theorems/LEDGER.csv` header-only.** Freezing is a later session (S003), which must cite the verified proof-source commit SHA created here.
>
> ## Non-negotiable scope
> - Same mathematics as the local proof: 8×8 board, two kings only, side to move, FIDE 2023 (https://handbook.fide.com/chapter/E012023), no tablebases, no engine oracles.
> - Lean verifies the *mathematical model*, not FIDE's normative text. The correspondence of model to rules (assumption A1, Articles 3.1–3.9, 5.2.2) remains a documented prose bridge; never claim Lean has verified the Laws of Chess.
> - Distinguish no-possible-mate (`Dead`) from no-forced-mate; distinguish `Arisen` from `Admissible`.
>
> ## Required work
> 1. **Toolchain.** Install Lean via `elan` if absent. Pin an exact stable `leanprover/lean4:vX.Y.Z` in `formal/lean-toolchain`; create `formal/lakefile.toml`. Prefer **no mathlib** unless it reduces trusted code; if used, pin its exact git revision in the lakefile and commit `lake-manifest.json`. Record `lean --version` and `lake --version`. If the toolchain cannot be installed (network/policy), stop, record exactly what failed, keep EC-C001 at `LOCAL_VERIFIED`, and install a remedial prompt.
> 2. **Definitions** (`formal/EndgameChess/KK.lean`, namespace `EndgameChess.KK`): `Square := Fin 8 × Fin 8`; `dInf`; `Colour`; `KKState` (white square, black square, side to move); `kingAttacks s q := dInf s q = 1`; `inCheck`; `Admissible`; `LegalKK p q` exactly as conditions (i)–(iii) of the proof, with the mover equal to the side to move and the turn flipped; `Checkmate c p` (side to move is `c`, in check, no `q` with `LegalKK p q`); `Reach` as an inductive reflexive–transitive closure (or `Relation.ReflTransGen` if mathlib is used); `Dead p`.
> 3. **Theorems**, mirroring the lemma names: `attack_iff_dInf_one` (if attack is defined via neighbour offsets, prove the equivalence; if defined as `dInf = 1`, say so explicitly), `not_inCheck_of_admissible` (L2), `admissible_of_legal_step` (L3; note it does not need admissibility of the source), `admissible_of_reach` (L4, induction including the zero-length case), `not_checkmate_of_reach` (L5), `dead_of_admissible` (L6/main theorem), and `admissible_of_last_move_legal` (L0 core: if a configuration is the result of a `LegalKK` step, it is admissible). Optionally `exists_legal_move_of_admissible` (R1).
> 4. **Proof method.** The main theorem must be proved by the invariant argument (induction on `Reach`), not solely by brute-force `decide` over all 8192 states. A separate kernel-checked `decide`/`native_decide` cross-check is allowed only if labelled as such; `native_decide` adds the `Lean.ofReduceBool` axiom and must never be used in the main theorem.
> 5. **Checks** (run them; record outputs verbatim in the closeout): clean `lake build` from a fresh checkout of the committed tree; `grep` for `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` in `formal/`; `#print axioms EndgameChess.KK.dead_of_admissible` (and L0 theorem) — expected only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) or none; record exactly what appears.
> 6. **Fidelity audit** `audits/EC-C001_KK_LEAN.md`: map each Lean definition/theorem to its prose counterpart; hostile check for weakened surrogates (e.g. `Dead` vacuous because `Reach` is empty or `Checkmate` unsatisfiable by definition — show `Checkmate` is satisfiable in some *non-admissible* state, e.g. adjacent kings with the side to move boxed in, or argue why not and what that means), off-by-one in `Fin 8` arithmetic, turn handling, and that `Dead` quantifies over all paths.
> 7. **CI.** Optionally add a Lean build job to `.github/workflows/` using the pinned toolchain; do not claim it passed unless a run result is actually observed.
> 8. **Status.** Only if steps 5–6 pass: EC-C001 → `FORMAL_VERIFIED` in `research/CANDIDATES.md`, recording the proof-source commit SHA, toolchain, declaration names and axiom output. Otherwise keep `LOCAL_VERIFIED` and state the blocker.
>
> ## Closeout
> Write `sessions/S002_KK_LEAN.md` and a `sessions/SESSION_LEDGER.md` row: changes, checks actually run (or not run), exact base and proof-source commit SHAs, toolchain versions, axiom output, candidate status, ledger effect (must be none). Install the next prompt in `NEXT_SESSION.md` and include it **in full** in the closeout: if Gate F passed, S003 = freeze EC-C001 as `EC-T0001` per `docs/PROOF_PROTOCOL.md` Gate Z (manifest under `theorems/frozen/EC-T0001/`, ledger row citing the earlier proof commit, `scripts/validate_ledger.py` passing); otherwise a targeted remedial S002 prompt. No novelty claims.
