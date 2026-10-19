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
