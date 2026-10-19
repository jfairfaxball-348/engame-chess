# NEXT SESSION — S025: Freeze the forcing and confinement prerequisites

**Owner instruction:** Execute S025 when the owner says "run next session" in this repository or pastes/links this prompt. Follow `AGENTS.md`: fetch latest `main`, merge unmerged session work first, and finish committed, pushed and merged to `main`. Publishing is part of the authorised session workflow.

## Ambitions and current mathematical boundary
- Ultimate ambition (unproved): an ultra-weak proof that standard chess has initial-position value draw, under a complete explicit rules model.
- Active milestone: proof-based outcome characterisations through seven pieces, without tablebases, whole-class enumeration or per-position certificates.
- K+R vs K L1 is frozen (EC-T0006/0007). The full clock-free forcing target EC-C011 remains **PROPOSED**. L1 liveness does not imply a forced win.
- S024 completed two prerequisites, **FORMAL_VERIFIED**, at proof-source commit `fca2ca88c8391b1d2bd49c3db9f2fa04258a4a87` on Lean `leanprover/lean4:v4.35.0`:
  - **EC-C009:** finite-rank forced-mate semantics, soundness, monotonicity, terminal inversion, choosing/defending rules and the dead-reply obstruction. New modules `Rules/ForcingDefinitions.lean`, `Rules/ForceMate.lean`.
  - **EC-C010:** every kernel-legal lone-king reply preserves a protected rook rank barrier when the strong king is strictly below the rook and the lone king above. New module `Rules/KRKConfinement.lean`. Includes arbitrary-reply completeness and the obstruction to a protected rook advance with a fixed king.
  - Fixed configurations in `Rules/KRKForcingExamples.lean` distinguish optional capture, stalemate, blocked rook rays and zero-/one-ply mate.
- Read `proofs/EC-C009_FORCING.md`, `proofs/EC-C010_KRK_CONFINEMENT.md`, `audits/EC-C009_C010_PAPER.md`, `audits/EC-C009_C010_LEAN.md`, `sessions/S024_KRK_FORCING.md` and `sessions/evidence/S024/README.md`, plus the charter, proof protocol and roadmap.

## Required Gate Z work
1. Re-verify the exact proof-source commit in a fresh GitHub checkout without `.lake`: `lake build`, `lake env lean AxiomCheck.lean`, and forbidden-token scan over the four new S024 modules. Save new Gate Z logs rather than relabelling S024's Gate F evidence. Ordinary hosts need no executable-path shim; this host's documented compatibility shim is in `theorems/frozen/EC-T0007/verification-environment.md` with retained source.
2. Inspect the exact statements and axioms for `mateWithin_sound`, `forceMate_not_dead`, `forceMate_no_moves_iff`, `dead_reply_not_forceMate`, `forceMate_choose`, `forceMate_defend`, `krk_protected_reply`, `rook_rank_barrier`, `krk_protected_rank_reply`, and `protected_rank_raise_unprotected`. Check the fixed examples too. The new declarations use subsets of the standard three axioms only. No frozen Lean source may be edited.
3. If and only if verification passes, freeze:
   - EC-C009 as **EC-T0008**, with `forceMate_defend` as the ledger's representative declaration and the full forcing-semantics theorem bundle explicitly listed in its immutable manifest;
   - EC-C010 as **EC-T0009**, with `krk_protected_rank_reply` as the representative declaration, plus the protected-reply completeness lemma, pure barrier lemma and advance obstruction in its manifest.
4. Record the proof-source SHA, exact `#check` outputs, rule scope, core-only toolchain, build/axiom evidence, source hashes and trust boundary. The host shim is an environment dependency, not a change to any Lean proof or kernel routine. The clock-free finite-rank game is a definition; do not present it as an already complete FIDE WDL model or claim an unproved equivalence with a separate strategy representation.
5. Append exactly two ledger rows, leaving earlier rows/manifests unchanged; update candidate status, theorem index, formal README, README and roadmap. Run ledger validation and the relevant Python suite. A failed Gate Z blocks the affected freeze and requires an exact remedial obligation.

## Remaining forcing problem (install S026 after successful freeze)
The next mathematical session must attack **EC-C011 on paper**, not repeat semantic setup or use the cooperative route as a forcing proof. Its first concrete obligations are:
- broaden rook safety beyond immediate king protection, for instance a rook too far for immediate capture or protected;
- prove the arbitrary-defender-reply version of the chosen invariant, accounting for optional rook capture;
- give explicit strong-side actions and a well-founded phase/region measure, with nonempty replies or actual mate checked in every branch;
- resolve the obstruction proved in S024: raising the rook with its king fixed below the old rank loses protection. A protected barrier alone is not a closed advancing strategy;
- attempt the general strong-to-move forcing theorem after a legal arrival, with all board-edge and stalemate exceptions handled. Derive weak-turn cases only after that result is proved, using the finite-branching defending rule. If incomplete, identify the precise missing progress/tempo lemma rather than claiming L2 or freezing a conditional restatement.

Keep the proof → audit → Lean → freeze order. No clock/repetition or full WDL claim until those layers exist.

## Closeout
Write `sessions/S025_FREEZE_EC-T0008_T0009.md` and a session-ledger row. Distinguish actually passed verification from unobserved CI, state the exact ledger effect, install S026 around the remaining forcing proof obligation with a full executable prompt, and include that prompt in the closeout. Commit, push and merge to `main`.
