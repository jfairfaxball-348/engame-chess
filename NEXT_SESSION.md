# NEXT SESSION — S016: freeze EC-C007 (dead K+R vs K: forced capture / stalemate) as EC-T0006, Gate Z

**Owner instruction:** Execute this S016 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C007 is `FORMAL_VERIFIED` (S015). Do not treat this prompt as evidence that it is frozen.

## Context
- Frozen: EC-T0001–EC-T0005. The template for a kernel-level freeze is S013 (`sessions/S013_FREEZE_EC-T0005.md`, `theorems/frozen/EC-T0005/`).
- EC-C007: proof [proofs/EC-C007_KRK_DEAD.md](proofs/EC-C007_KRK_DEAD.md); audits [audits/EC-C007_KRK_DEAD.md](audits/EC-C007_KRK_DEAD.md) and [audits/EC-C007_KRK_DEAD_LEAN.md](audits/EC-C007_KRK_DEAD_LEAN.md). Lean module `formal/EndgameChess/Rules/KRK.lean`; **proof-source commit `570dfa73685ea0cc98a4ab4eaf01b5f0a1edabc4`** (S015).
- **Local Lean is primary:** elan default `leanprover/lean4:v4.34.1`. Push as `jfairfaxball-348`, using the repo-local Git Credential Manager config and `GCM_INTERACTIVE=never`.
- On Windows the working copy is CRLF (`core.autocrlf=true`). Hash modules from committed blobs (`git show <sha>:<path> | sha256sum`), and check the ledger in the staged blob (`git show :theorems/LEDGER.csv`): no CR, and earlier rows a byte-identical prefix.

## Required work
1. **Fresh-clone verification** of `570dfa7…` from GitHub, with no `.lake`: run `lake build` and `lake env lean AxiomCheck.lean` locally. Save the outputs (CR-stripped) as `theorems/frozen/EC-T0006/lake_build.log` and `axioms.log`. Confirm that all axiom reports ⊆ `[propext, Classical.choice, Quot.sound]`, and that there is no `sorryAx`/`ofReduceBool` and no forbidden token.
2. **Manifest** `theorems/frozen/EC-T0006/v1.md`, following EC-T0005. It covers:
   - statement: prose, plus Lean verbatim for `krk_dead_of_forced_capture`, `krk_forced_capture_drawn_by_rule` and `dead_of_succ_KK`, and the `IsKRK`/`krkBoard` source;
   - the remark that the Lean statement is stronger than the prose (`IsKRK` and the turn are unused);
   - dependency on EC-T0003;
   - non-vacuity: the forced capture via Rb3–b2, the stalemate, and the live contrast;
   - SHA-256 of `Rules/KRK.lean` and of all imported modules (`Rules/KNK.lean` is EC-T0005, unchanged), plus the bridge hash;
   - the verification record and the trust boundary;
   - the open companion EC-C008 (`PROPOSED`).
3. **Ledger:** one `FROZEN` row `EC-T0006` citing `570dfa73685ea0cc98a4ab4eaf01b5f0a1edabc4`, with declaration `EndgameChess.Rules.krk_dead_of_forced_capture` and file `formal/EndgameChess/Rules/KRK.lean`. `validate_ledger.py` must report 6.
4. Update `theorems/README.md` (count 6), `research/CANDIDATES.md`, `README.md`, `docs/ROADMAP.md` and `formal/README.md`.

## Next prompt to install at closeout: S017 = EC-C008 paper proof (Gate L)
Write S017 in full. Objective: prove on paper that every K+R vs K position with the **strong side to move** that was produced by a legal move is **not dead** (cooperative mate reachable). With EC-C007 this characterises the dead K+R vs K positions exactly. Requirements for S017:
- An explicit cooperative mating route with a complete legality case analysis. The plan in EC-C007 §6:
  1. the rook goes to the corner farthest from the lone king (≤ 2 rook moves, never giving check);
  2. the lone king walks to the near corner;
  3. the strong king takes the opposition two squares away;
  4. a rook tempo fixes the parity;
  5. the rook mates along the edge.
- Handle the obstacles the plan must survive: the strong king blocking the rook's path; the lone king shielded on the rook's line by the strong king; stalemate or forced capture en route (the route must always leave the lone king a non-capturing legal move); and parity.
- **Strategy simulator:** write a deterministic strategy simulator in Python that plays the route from every strong-to-move state (both orientations) and checks that it reaches mate with every move legal. Use it to find the failing cases while designing the route, then prove the route correct on paper. The simulator is supplementary, never the proof.
- A route expressible as a small number of move schemas with legality lemmas, so that a later Lean formalisation is feasible.
- Hostile audit. EC-C008 → `LOCAL_VERIFIED` only if no gap remains.

## Closeout
`sessions/S016_FREEZE_EC-T0006.md` and a `sessions/SESSION_LEDGER.md` row (ledger effect **+1 → EC-T0006**, 6 frozen). Install S017 in full. Commit, push, merge to `main`.
