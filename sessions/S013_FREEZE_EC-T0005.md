# S013 — Freeze EC-C003 → EC-T0005 (K+N vs K over the rules kernel, Gate Z)

**Date:** 2026-10-18
**Type:** Freeze session. No change to mathematics or Lean source.
**Base revision:** `fe24f0c` (`main`, S012 closeout).
**Proof-source commit cited:** `3adcebbb4ae643a62c8bf18b478bf70da774dbf8` (S012).
**Freeze commit:** the S013 commit on branch `claude/s013-freeze-ec-t0005`, merged to `main`. It does not cite its own SHA.

## Changes
- `theorems/frozen/EC-T0005/v1.md` (new): statement (prose; Lean verbatim `#check` of `dead_of_legal_into_KNK`, `arisen_KNK_dead`, `knk_drawn_by_rule`; `#print Rule5_2_2`; the `IsKNK` definition), relation to EC-T0003, the S011 prompt correction, evidence, 13 module hashes + bridge hash, verification record, trust boundary. `lake_build.log` and `axioms.log` beside it.
- `theorems/LEDGER.csv`: one new row **EC-T0005** citing `3adcebb…`. Earlier rows byte-identical in the committed (LF) blob; no CR in the blob.
- `theorems/README.md` (count 5), `research/CANDIDATES.md`, `README.md`, `docs/ROADMAP.md` (rung 4 now opens with possible mate), `formal/README.md`.
- `NEXT_SESSION.md`: S014 (K+R vs K possible mate, EC-C007, Gate P + L) installed.

## Checks actually run (local, owner's machine, Lean 4.34.1)
- Fresh `git clone` from GitHub, checkout `3adcebb…`, no `.lake`: `lake build` exit 0, `Build completed successfully (16 jobs)`.
- `lake env lean AxiomCheck.lean`: exit 0; 92 reports all ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx`/`ofReduceBool`.
- Word-bounded forbidden-token grep over `formal/**/*.lean` in the clone: no matches.
- Module hashes (from committed blobs): the 12 modules frozen with EC-T0003/0004 match the EC-T0004 manifest exactly; `git diff 573c96a 3adcebb -- formal/EndgameChess/` adds only `Rules/KNK.lean`.
- `python scripts/validate_ledger.py`: `LEDGER VALID: 5 frozen theorem(s) (structure only)`.
- Remote CI: not observed.

## Findings
- **Frozen:** EC-T0005.
- **Observed while scoping S014 (not proved, not tested yet):** a legal K+R vs K position can be dead (Black Ka1, White Rb2 unprotected, White Kh8, Black to move: the only legal move captures the rook). Recorded as the starting point of S014.

## Ledger effect
**+1 → EC-T0005 FROZEN** (5 frozen theorems).

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S014: K+R vs K, possible mate — which K+R vs K positions are dead? (Gate P + Gate L, over the rules kernel)
>
> **Owner instruction:** Execute this S014 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. Nothing in this prompt is a proved result.
>
> ## Context
> - Frozen: EC-T0001–EC-T0005 (K vs K, K+B vs K, K+N vs K; the last three over the general rules kernel `formal/EndgameChess/Rules/`).
> - Roadmap rung 4 is K+R vs K. Its eventual question is **forcing** (does the strong side force mate?). The charter insists that "no possible mate", "no forced mate" and "draw under the rules" are different predicates. So rung 4 opens with **possible mate** (cooperative reachability, `¬DeadK`), which is a prerequisite and is *not* trivially "always live".
> - **Observation to check first (not yet verified):** not every legal K+R vs K position is live. Example: Black Ka1, White Rb2 (unprotected), White Kh8, Black to move. Black is not in check; a2 and b1 are covered by the rook; the only legal move is Kxb2, giving K vs K, which is dead (EC-T0003). So this position should be `DeadK`.
> - **Local Lean is primary** (elan default `leanprover/lean4:v4.34.1`); push as `jfairfaxball-348` (repo-local credential config). No Lean is required this session.
>
> ## Objective
> Register and prove on paper (Gate L) a **characterisation of dead K+R vs K positions** over the kernel, for positions produced by a legal move (any predecessor material, any flags, either orientation). Plan its Lean statement for S015. Ledger unchanged.
>
> ## Proposed candidate (Gate P — refine before proving; record in `research/CANDIDATES.md` as **EC-C007**)
> Let `IsKRK q σ sk rs wk` be the K+R vs K analogue of `IsKNK` (rook of colour σ on `rs`). For `q` produced by a legal move:
> - **(a) Strong side to move ⇒ not dead:** some finite series of legal moves from `q` reaches a checkmate.
> - **(b) Weak side to move:** `DeadK q` iff `q` is not checkmate and **every** legal move of the weak king captures the rook (this includes stalemate, where there are no legal moves at all).
> Check this conjecture against the diagnostic **before** trying to prove it, and correct it if it fails (record any correction, as S011 did). Pay attention to: castling flags (a rook on its home square with a castling right and the strong king on e1/e8 — can castling ever be legal here? the kernel requires both king and rook on original squares and the right), the strong side being stalemated (impossible? the rook always has a move?), positions where the rook is attacked and every rook move or king move abandons it, and mates already on the board.
>
> ## Required work
> 1. **Diagnostic** `scripts/krk_diagnostic.py` + unit test, written independently of the proof (rook rays walked square by square, as in `kbk_diagnostic.py`; Art. 3.3 + 3.5):
>    - all placements, both orientations, both sides to move; legal states (side not to move not in check);
>    - counts: checks, checkmates, stalemates, forced rook captures;
>    - **cooperative reachability**: the set of legal states (K+R vs K ∪ K vs K) from which some checkmate is reachable, computed as a fixpoint over the diagnostic's own move graph (a cooperative-reachability computation over the script's own generator — supplementary evidence only, not a tablebase, never cited as proof); compare its complement with the conjectured characterisation, position by position;
>    - **mutation test:** e.g. forbid captures of the rook, or replace the rook by a bishop; the characterisation must then visibly fail or change.
> 2. **Proof** `proofs/EC-C007_KRK_LIVE.md`, self-contained:
>    - (b) "⇐" is easy (every successor is K vs K, dead by EC-T0003; and `q` itself is not mate).
>    - (b) "⇒" and (a) need explicit **cooperative mating routes**: from any strong-to-move legal K+R vs K position, a concrete sequence of legal moves (both sides cooperating) ending in mate. Find a uniform construction (e.g. walk the rook to safety, march the kings to a fixed mating pattern near a corner or edge, then mate), with a complete case analysis of obstacles (the rook blocking its own king, the weak king being stalemated en route, the weak king forced to capture). Prefer a construction whose Lean formalisation is feasible: a bounded number of explicit move schemas, each with a legality lemma.
> 3. **Audit** `audits/EC-C007_KRK_LIVE.md` (hostile): corners/edges, both orientations, both sides to move, castling flags, stalemate en route, zero-length path (`q` already mate), rook capture branches, every symmetry used.
> 4. **Status:** EC-C007 → `LOCAL_VERIFIED` only if no gap remains; otherwise `PROPOSED` with the gap stated. Record the planned Lean statements for S015 (`Rules/KRK.lean`): e.g. `krk_strong_to_move_live`, `krk_dead_iff`.
>
> ## Closeout
> `sessions/S014_KRK_LIVE.md` and a `sessions/SESSION_LEDGER.md` row: changes; proved / tested / conjectured separately; checks actually run; base and result SHAs; candidate status; ledger effect (none). Install the next prompt in full: if Gate L passes, S015 = Lean formalisation of EC-C007 over the kernel (Gate F); otherwise a remedial S014. Commit, push, merge to `main`.
