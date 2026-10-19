# S026 — Distant rook safety and all-defences checking progress

**Date:** 2026-10-19. **Base:** `b03a979d93c7811cc1579644ebcfb60201a6930b` (`main` after S025). Initial fetch found no unmerged remote session branches and a clean tree.
**Proof-source:** `e8daef6daee088c3adaf1c21b51c0a8f1e31103d`, published on `session/s026-krk-forcing-progress` before exact-source verification. Closeout follows that commit. Publication uses the connected jfairfaxball-348 GitHub account because the shell transport lacks credentials.

## Result

- **EC-C012 FORMAL_VERIFIED:** a rook distant from the lone king or protected by the strong king cannot be captured in any legal lone-king reply. Every reply is a non-capturing geometric king step in KRK. Includes the extended rank barrier and a nondeadness bridge when a legal reply exists. A complete capture-availability equivalence is not claimed.
- **EC-C013 FORMAL_VERIFIED:** from same-file kings two ranks apart, strong to move, with the rook at least four files away and off the lone king's rank, a chosen check either mates at the top edge or every defending reply rises exactly one rank. The chosen king-up follow-up has a nonempty reply set, and every second reply leaves a distant-rook separating barrier with strictly smaller `7 - weakRank`. This is an explicit four-ply all-defences phase, not an assumed winning continuation.
- A general upper-edge **ForceMate** family is proved, not only a fixed mate-in-one example. The game is clock-free/repetition-free with the frozen finite-rank semantics.
- **EC-C011 remains PROPOSED.** The phase does not establish arbitrary-position setup, re-entry into opposition, a complete repeatable strategy, full KRK WDL, clock outcomes or a distance theorem.
- **Ledger effect: none — 9 frozen theorems.** All frozen proof/definition modules and earlier ledger/manifests remain unchanged.

## Sustained strategy attempt and exact gap

S024's fixed-king protected-rook advance failed. Distant safety resolves that obstacle for the checking phase: the rook can be unprotected but too far to capture. The four-file margin absorbs two defending file steps. A margin of two permits Rc3+ Kb4 Ka2 Kxc3; three permits Rd3+ Kb4 Ka2 Kc4 with the rook en prise. Both failures are kernel-checked.

The successful phase can return Ka2/Rh3/Kc4, with the kings not opposed. Repeating the phase immediately would violate its entry hypotheses. The remaining policy must force re-entry or another strict contraction, using a real setup/tempo measure and handling edge changes and stalemate. The suggested narrow phase-image family is recorded for the next proof attempt; image bounds must be established before formal reuse. Safe setup from arbitrary legal strong-to-move arrivals remains separate. See `research/S026_STRATEGY_ATTEMPT.md`.

All nonterminal phase nodes are live by the safe/nonempty weak-state bridge and EC-T0007 for strong-turn successors. No argument relies on continuing after a dead draw. No independent external audit, novel chess claim, tablebase, engine or whole-class proof enumeration is used.

## Changes

Two standalone proofs, same-agent paper and formal fidelity audits, three new Lean modules (`Safety`, `CheckProgress`, `Examples`), aggregate/axiom imports, candidate register and current status updates. A local diagnostic uses the existing independent move generator on 24 curated inputs and their immediate reply trees only; it does not invoke the class-wide graph/fixpoint routine. S027 freezes the completed prerequisites before the next setup/re-entry proof.

## Checks actually run

- Working incremental build: 29 jobs, exit 0. New CheckProgress module took about 64 seconds locally. An earlier overlarge arithmetic proof was restructured; only the final successful source is the proof anchor.
- Fresh GitHub clone detached at the exact proof-source, no `.lake`: `lake build` exit 0, 29 jobs, 296.85 seconds.
- `lake env lean AxiomCheck.lean`: exit 0 at `2026-10-19T08:00:05Z`. All 197 reports checked against allowed sets (174 standard-three, 10 propext/Quot.sound, 8 propext-only, 5 axiom-free); 17 declarations added. Working/clean content matches exactly.
- Forbidden-token scan: 0 in the three new modules. SHA-256 hashes checked against closeout source. No frozen module drift.
- Three false safety/re-entry claims rejected by Lean. Fixed positive margin/capture/re-entry controls compiled in the normal build.
- `python3 scripts/krk_check_phase_diagnostic.py`: 24 chosen configurations in both colours; 8 mates, 44 first replies and 194 second replies; two failed-margin controls. Supplementary only.
- `python3 -m unittest discover -s tests`: all 33 passed, 139.226 seconds.
- `python3 scripts/validate_ledger.py`: 9 frozen theorems, structure only. `git diff --check` before commit.
- Core-only Lean 4.35.0 release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; same retained executable-path compatibility shim as prior sessions. No proof, compiler or kernel routine replaced. Hosted CI is not asserted as observed.

Full evidence: `sessions/evidence/S026/`. The ultra-weak initial-position ambition and seven-piece milestone remain unchanged; this session does not establish them.

## Installed next-session prompt (full text)

# NEXT SESSION — S027: Freeze distant safety and the checking-progress phase

**Owner instruction:** Execute S027 when the owner says "run next session" in this repository or pastes/links this prompt. Follow `AGENTS.md`: fetch latest `main`, merge unmerged session work first, and finish committed, pushed and merged to `main`. Publication is part of the authorised session.

## Ambitions and current boundary
The unproved ultimate ambition is an ultra-weak draw proof for initial-position chess. The active milestone remains proof-based seven-piece outcome characterisations, without tablebases or class-wide enumeration. K+R vs K L1 is frozen. **The general forcing target EC-C011 is still PROPOSED.**

S026 completed two prerequisites at **proof-source `e8daef6daee088c3adaf1c21b51c0a8f1e31103d`**, core-only Lean `leanprover/lean4:v4.35.0`:
- **EC-C012:** distant-or-protected rook safety for every legal lone-king reply, the extended rank barrier and a nondeadness bridge. `formal/EndgameChess/Rules/KRKForcing/Safety.lean`.
- **EC-C013:** the exact opposed-kings four-ply checking phase, with every first/second reply covered, explicit nonempty reply sets, strict rank progress and a distant-rook barrier at the end. The upper-edge branch forces mate. `Rules/KRKForcing/CheckProgress.lean`.
- Fixed controls in `Rules/KRKForcing/Examples.lean`: two-file margin loses the rook, three-file margin can leave it hanging, and a successful phase need not restore opposition. The 24 local diagnostic samples are supplementary only.

Read the charter/proof protocol, both S026 paper proofs and audits, the S026 closeout and `sessions/evidence/S026/README.md`, then inspect the exact source statements. These are FORMAL_VERIFIED, not frozen, until Gate Z passes.

## Required Gate Z work
1. Fresh GitHub checkout at the proof-source SHA, no `.lake`: `lake build`, `lake env lean AxiomCheck.lean`, and forbidden-token scan over all three new S026 modules. Retain **new** Gate Z logs. This host's executable-path shim is documented and retained with EC-T0007; it changes no compiler, kernel routine or proof. Ordinary hosts may omit it.
2. Inspect statements and axioms for `krk_safe_reply`, `krk_safe_rank_reply`, `krk_safe_weak_live`, `krk_opposition_check`, `krk_follow_check`, `krk_opposition_four_ply`, `krk_opposition_edge_force`, and their supporting geometric lemmas/examples. The source's full report has 197 declarations, all within the standard allowed axiom sets. Quote exact `#check` outputs in the manifests.
3. If verification passes, freeze **EC-C012 as EC-T0010**, representative declaration `EndgameChess.Rules.krk_safe_reply`, and **EC-C013 as EC-T0011**, representative `EndgameChess.Rules.krk_opposition_four_ply`. List the complete bundles, exact hypotheses and definitions, proof-source SHA, source hashes, toolchain, rule scope, axiom findings, evidence and trust boundary. No Lean source edits in this freeze session; any defect blocks the affected freeze and requires a precise remedial prompt.
4. Append exactly two ledger rows, leaving all nine earlier rows/manifests unchanged. Update candidate status, theorem index, README, formal README and roadmap. Run ledger validation and the relevant Python suite. The expected frozen count after success is **11**; this is not 11 solved endgame classes.
5. Make the scope conspicuous: a four-file rook margin, same-file kings two ranks apart, strong turn, rook off the lone king's rank, both colours and arbitrary flags. The phase forces a useful contraction in this family, not general KRK WDL or a complete repeatable strategy. No clocks/repetition or initial-position claim.

## Install S028 around the actual missing proof
After successful freeze, the next mathematics session must attack setup/re-entry, not repeat definitions or treat this phase as a finished strategy.

The phase leaves a distant-rook separating barrier but can lose opposed files (the legal Ka2/Rh3/Kc4 witness). Investigate the narrower phase-image family suggested by two king replies: rook one rank above the strong king, lone king one or two ranks above the rook, lone/strong file offset at most two, rook/strong file separation at least four, and rook/lone distance at least two. **Prove the image bounds before relying on them**; the main frozen result alone must not be silently strengthened.

Prove an explicit finite all-defences policy from the stated family to actual mate, a correctly oriented opposed entry state for EC-T0011, or another strict region contraction. Supply a well-founded phase/tempo measure and handle corners, waiting moves, rook en prise, changing axes and stalemate. Merely chasing the lone king's file or preserving a wall does not prove termination. Then attack safe setup from arbitrary strong-to-move legal KRK arrivals. New lemmas must import the frozen modules without editing them. Keep EC-C011 PROPOSED until every part is closed; record the exact remaining gap if the complete proof still resists the attempt.

## Closeout
Write `sessions/S027_FREEZE_EC-T0010_T0011.md` and the session-ledger row, distinguish actual checks from unobserved CI, install a full executable S028 prompt around the remaining mathematical obligation, include that prompt in the closeout, and commit/push/merge to `main`.
