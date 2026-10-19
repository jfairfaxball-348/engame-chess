# S024 — K+R vs K forcing semantics and first all-defences prerequisite

**Date:** 2026-10-19. **Base:** `4a2c40efb09d85c8c3bbcd1f0e7f5e22ad31da90` (`main` after S023 publication). No unmerged remote session branches were found at session start.
**Proof-source:** `fca2ca88c8391b1d2bd49c3db9f2fa04258a4a87`. Published on the session branch before fresh verification; the closeout commit follows it. Branch: `session/s024-krk-forcing`. The connected jfairfaxball-348 GitHub account is used for publication because the shell transport lacks credentials.

## Outcome

- **EC-C009 FORMAL_VERIFIED:** finite-rank forcing semantics over the kernel, soundness, budget monotonicity, zero-ply terminal inversion, one-step choosing/defending rules (including finite-branching bounds), and the dead-reply obstruction.
- **EC-C010 FORMAL_VERIFIED:** every arbitrary legal lone-king reply preserves a rook-protected separating rank when the strong king is strictly below and the lone king above. All-kernel-reply completeness is proved; model soundness alone is not used to assume all defences are covered.
- **EC-C011 PROPOSED:** general clock-free KRK forced-mate/outcome target. No full strategy, safe setup or strict progress lemma has been established.
- **Ledger effect: none.** Still 7 frozen theorems. Source modules, earlier frozen manifests and ledger rows remain unchanged. The only existing Lean files edited are the aggregate and axiom-check entry points.

## Mathematical findings and attempt

White Kh8/Rb3 against Black Ka2, Black to move: Kxb3 and Ka1 are kernel-legal. The first gives dead K vs K; the second is live by EC-T0007. Thus the starting state is live but White does not satisfy the forcing predicate; Black has an explicit holding action. Global reachability is not asserted.

A protected rook's rank is an uncrossable barrier only with the strong king strictly off that rank: Ke4/Rd4/Kg5 permits Kg4 because the king blocks the rook. Kc6/Rb7/Ka8 satisfies the protected-rank invariant yet is stalemate. These are proved fixed witnesses, not whole-class enumeration. Positive one-ply mate, zero-ply mate and wrong-winning-colour controls are included too.

The first attempted progress rule (raise the rook while keeping its king fixed below) fails: a higher rook is at least two ranks from that king and loses protection. `protected_rank_raise_unprotected` proves this general obstruction. A larger distant-or-protected safety invariant and a verified tempo/progress phase are needed; see `research/S024_STRATEGY_ATTEMPT.md`. No failure of a proposed protected advance is misrepresented as impossibility of rook mate.

## Changes

New symbolic proofs `proofs/EC-C009_FORCING.md`, `proofs/EC-C010_KRK_CONFINEMENT.md`; same-agent hostile paper/fidelity audits; four new Lean modules (`ForcingDefinitions`, `ForceMate`, `KRKConfinement`, `KRKForcingExamples`); aggregate imports and axiom reports. Candidate register, README, formal README and roadmap updated; S025 installed to freeze the completed prerequisites before further research. The ultra-weak initial-position ambition and seven-piece milestone remain unchanged. No novelty or independent external-review claim.

## Checks actually run

- Working incremental build: 26 jobs, exit 0.
- **Fresh GitHub clone** detached at the proof-source commit, no `.lake`: `lake build`, 26 jobs, 236.09 seconds, exit 0.
- Exact-source `lake env lean AxiomCheck.lean`: exit 0 at `2026-10-19T06:56:09Z`; 180 reports, all standard-three subsets; 19 new reports. Exact statement output and axiom sets retained. Clean and working reports byte-identical apart from the separately added completion metadata.
- No forbidden proof escapes in the four new modules; SHA-256 source hashes retained and checked. No frozen module drift.
- Three false fixed-configuration claims rejected by Lean: blocked-ray crossing illegal, optional declining move illegal, protected-rank stalemate in check.
- `python3 -m unittest discover -s tests`: 33 tests passed, 142.963 seconds.
- `python3 scripts/validate_ledger.py`: 7 frozen theorems, structure only.
- Toolchain core-only Lean 4.35.0, release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Same retained executable-path shim as S023; official binaries and kernel unmodified.
- Remote CI not asserted as observed. Gate F evidence is in `sessions/evidence/S024/`. Gate Z has not been run for EC-C009/010.

The new predicate is a finite-rank clock-free/repetition-free reachability game, stopped at mate/stalemate/deadness. It does not supply a full FIDE WDL model or claim an unproved equivalence with a separate strategy representation. No clock rule, distance, seven-piece parity or initial-position value claim follows.

## Installed next-session prompt (full text)

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
