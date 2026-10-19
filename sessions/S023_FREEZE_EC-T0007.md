# S023 — Gate Z freeze of EC-C008 as EC-T0007

**Date:** 2026-10-19. **Base:** latest `main`, `86d1d573e07e46fd0c0c1375a3fcd320034438d9` (including the owner's ultra-weak ambition update). No unmerged remote session branches were found by `git branch -r --no-merged origin/main`.
**Proof-source:** `a8bc161d2a51b92c340697af16a10e874cd9a098`. This session changes no Lean module. Session branch: `session/s023-freeze-ec-t0007`; closeout and freeze evidence are committed together, then fast-forward merged to local `main`. The owner explicitly authorised publication on 2026-10-19 after the initial approval block.

## Result and ledger effect

**EC-C008 → FROZEN as EC-T0007.** The new manifest is `theorems/frozen/EC-T0007/v1.md`. The ledger gains exactly one row citing the existing proof-source commit: **7 frozen theorems**. All earlier ledger rows and frozen records are unchanged.

Together with EC-T0006, the result completes K+R vs K layer L1 over the declared FIDE 2023 kernel: strong-to-move after a legal arrival is live; lone-king-to-move is dead iff not mate and every legal move captures the rook. Arisen positions have the corresponding Art. 5.2.2 characterisation. This is possible mate, not forced mate.

## Checks actually run

- Fresh clone from GitHub, detached at the exact proof-source commit; no `formal/.lake` before build.
- Official Lean 4.35.0 release, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; no project dependencies.
- `lake build`: exit 0, 22 jobs, 208.00 seconds. `Reply.lean`: 123 seconds. Full log saved in the freeze directory.
- `lake env lean AxiomCheck.lean`: exit 0; all 161 reports inspected by allowed-axiom set, including 5 axiom-free declarations. Both main declarations and both rule/arisen corollaries use exactly the standard three axioms. Exact `#check` output retained in log and manifest.
- Forbidden-token scan on `Rules/KRKLive/*.lean`: zero matches. Full Lean source SHA-256 inventory retained. Main's Lean sources match the proof commit.
- Host startup issue resolved by an executable-path compatibility shim: `/proc/<own-pid>/exe` is denied here, `/proc/self/exe` works. The retained `proc-path.c` changes only that `readlink` query. It changes no Lean proof, axiom, elaborator or kernel routine. See `verification-environment.md`; ordinary hosts omit it.
- `python3 -m unittest discover -s tests`: 33 tests passed (142.452 seconds).
- `python3 scripts/validate_ledger.py`: 7 frozen theorems, structure only.
- `git diff --check`: passed before commit.
- Remote CI: not observed; the fresh local proof-source build is the Gate Z evidence.

## Other changes and remaining work

Updated README, formal README, theorem index, candidate register and roadmap. The owner's ultra-weak draw ambition and proof-based seven-piece milestone remain in place. The next rung is **K+R vs K L2**, beginning with precise alternating-game semantics and one general forcing prerequisite. The roadmap's earlier shorthand "strong side wins whenever not dead" has been corrected: an optional rook capture may draw a live position. S024 must verify this distinction in the kernel and state the correct candidate.

No new mathematical result beyond the existing verified EC-C008 is claimed in S023. No forcing strategy, full WDL characterisation, clock/repetition result, distance result, tablebase parity or initial-position value has been proved. External independent audit remains open. Frozen sources are now protected by the existing protocol.

## Publication boundary

The push to `origin session/s023-freeze-ec-t0007` was rejected by automatic approval review: it considered the remote unverified and the instruction "run next session" insufficient authorization to disclose the repository contents and new freeze artifacts. No alternate transport was attempted before approval. The owner then replied "Yes push" on 2026-10-19. The shell Git transport lacked credentials, so the authorised publication uses the connected jfairfaxball-348 GitHub account. Publication preserves the verified proof-source SHA and all freeze evidence.

## Installed next-session prompt (full text)

# NEXT SESSION — S024: K+R vs K forcing semantics and the first L2 proof

**Owner instruction:** Execute S024 when the owner says "run next session" in this repository or pastes/links this prompt. Follow `AGENTS.md`: fetch, start from latest `main`, merge any unmerged session branch first, and finish with the session committed, pushed and merged to `main`.

## Objectives and starting point
- Ultimate ambition (unproved): ultra-weakly establish that standard chess has initial-position value draw, under a complete explicit rules model. See `docs/CHARTER.md`.
- Active milestone: proof-based outcome characterisations for every ending with fewer than 8 pieces, without tablebase lookup or per-position enumeration.
- EC-T0006 and EC-T0007 settle K+R vs K **L1** (dead/live). This is cooperative reachability, not optimal play. The frozen KRKLive modules must not be edited.
- S024 advances to **L2**, starting with precise forcing semantics and one tractable geometric prerequisite. Proof first, then formalisation, then freeze.

## Read first
`docs/CHARTER.md`, `docs/PROOF_PROTOCOL.md`, `docs/ROADMAP.md`, `docs/RULES_KERNEL.md`; `theorems/frozen/EC-T0007/v1.md`; `proofs/EC-C008_KRK_LIVE.md`; `formal/EndgameChess/Rules/{Reach,Outcome,KRK}.lean`; `formal/EndgameChess/Rules/KRKLive/{Basic,Endgame,Reply,Relocation,Main}.lean`.

## Required work
1. **Fix the game and quantifiers before proposing a theorem.** Define a turn-based, forced-mate predicate over kernel `Legal`, with a named winning colour. The winning side chooses a legal successor; the defending side must have a legal move and every legal successor must satisfy the continuation obligation. Checkmate of the defender is the winning base case. Stalemate and dead positions cannot become wins through an empty universal quantifier; zero-length mate must be treated correctly. Explain whether a well-founded inductive attractor or a strategy plus natural-valued rank is used, and prove their correspondence if both are needed.
2. **Pin the scope.** The first forcing result is in an explicitly clock-free and repetition-free game, stopped at mate/stalemate/deadness. The existing kernel has no half-move clock or repetition history. Do not claim FIDE WDL, Syzygy WDL/DTZ, or a full-game result until their rule layers and proofs exist.
3. **Audit the tempting false statement:** "every live K+R vs K position is a forced win for the rook side." A legal *optional* rook capture can lead to a drawn K vs K successor even if a different move preserves a route to mate. Test White Kh8, Rb3, Black Ka2, Black to move: compare Kxb3 with Ka1 using the local kernel. Record the exact move-legality and liveness evidence, and avoid claiming global reachability unless proved. The future WDL criterion must distinguish any available capture from an unavoidable capture, stalemate and checkmate.
4. **Register the corrected L2 candidate(s)** with exact hypotheses, turn, quantifiers, terminal cases, flags and capture behaviour. In particular, investigate the strong-to-move winning statement and the weak-to-move branches separately; do not promote either on chess folklore alone.
5. **Attempt the first general paper proof** toward a forcing KRK strategy: for example a safe-rook confinement invariant and a well-founded decrease of the lone king's available rectangle, including waiting moves, checking moves, rook safety and stalemate avoidance. Reuse frozen geometry through imports. A cooperative reply lemma cannot discharge an all-defences obligation. Aim to close one precise prerequisite completely; if the whole strategy is tractable, continue through its proof and adversarial audit.
6. Write a standalone proof and hostile audit for any claim marked `LOCAL_VERIFIED`. Explicitly test board edges, both colours, side to move, hanging rook, capture, zero-length mate and stalemate. Local diagnostic scripts are supplementary only; no tablebases, engine oracles, whole-class enumeration proof or per-position certificate proof.
7. Formalise only statements whose mathematics is locked. New modules only; add main declarations to `AxiomCheck.lean`, compile changed modules/importers, and inspect axioms. If a paper gap remains, leave the candidate `PROPOSED` and identify the exact missing lemma. Do not write a tautological conditional theorem as a substitute for the target.

## Closeout
Run relevant Python checks and `python3 scripts/validate_ledger.py`. Do not change the frozen ledger without a separate completed Gate Z. Write `sessions/S024_KRK_FORCING.md` and the session-ledger row; distinguish proved, formalised, tested and open findings. Install the next session around the actual remaining proof obligation, include its full prompt in the closeout, and commit/push/merge to `main`. No speculative initial-position solving detour and no packaging-only migration in place of the active mathematical rung.
