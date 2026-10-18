# S016 — Freeze EC-C007 → EC-T0006 (dead K+R vs K: forced capture / stalemate, Gate Z)

**Date:** 2026-10-18
**Type:** Freeze session. No change to mathematics or Lean source.
**Base revision:** `bce2b3c` (`main`, S015 closeout).
**Proof-source commit cited:** `570dfa73685ea0cc98a4ab4eaf01b5f0a1edabc4` (S015).
**Freeze commit:** the S016 commit on `claude/s016-freeze-ec-t0006`, merged to `main`. It is not self-cited.

## Changes
- `theorems/frozen/EC-T0006/v1.md` (new). It contains:
  - the statement, in prose and as verbatim Lean `#check`s;
  - the definitions;
  - a strength remark;
  - non-vacuity witnesses;
  - the relation to EC-T0003 and to the open EC-C008;
  - 15 module hashes plus the bridge hash;
  - the verification record and trust boundary.
  `lake_build.log` and `axioms.log` sit beside it (CR-stripped).
- `theorems/LEDGER.csv`: one new row **EC-T0006**. In the staged blob, earlier rows are a byte-identical prefix and there is no CR.
- `theorems/README.md` (count 6), `research/CANDIDATES.md`, `README.md`, `docs/ROADMAP.md` and `formal/README.md` updated.
- `NEXT_SESSION.md`: S017 (EC-C008 paper proof) installed.

## Checks actually run (local, Lean 4.34.1)
- Fresh GitHub clone at `570dfa7`, no `.lake`: `lake build` exit 0, 17 jobs.
- `lake env lean AxiomCheck.lean`: exit 0, 101 reports, all standard; no `sorryAx`/`ofReduceBool`.
- Forbidden-token grep over `formal/**/*.lean`: none.
- Hashes: the 13 modules from earlier freezes are identical to the EC-T0005 manifest. `git diff 3adcebb 570dfa7 -- formal/EndgameChess/` adds only `Rules/KRK.lean`.
- `python scripts/validate_ledger.py`: `LEDGER VALID: 6 frozen theorem(s) (structure only)`.
- Remote CI: not observed.

## Ledger effect
**+1 → EC-T0006 FROZEN** (6 frozen theorems).

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S017: EC-C008 paper proof — K+R vs K with the strong side to move is never dead (Gate L, over the rules kernel)
>
> **Owner instruction:** Execute this S017 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C008 is `PROPOSED`. Nothing in this prompt is a proved result.
>
> ## Context
> - Frozen: EC-T0001–EC-T0006. **EC-T0006** (S016) proves one direction: a K+R vs K position with the lone king to move, not mate, in which every legal move captures the rook (or which is stalemate), is dead.
> - **EC-C008** (the converse; see [proofs/EC-C007_KRK_DEAD.md](proofs/EC-C007_KRK_DEAD.md) §6 and `research/CANDIDATES.md`): let `q` be produced by a legal move, with `IsKRK q σ sk rs wk`.
>   - (a) If `q.turn = σ`, then `¬DeadK q`.
>   - (b) Hence, if `q.turn = σ̄`: `DeadK q` iff `q` is not mate and every legal move captures the rook.
>   - (b) follows from (a) plus EC-T0006: a non-capturing lone-king move leads to a strong-to-move K+R vs K position produced by a legal move.
> - **Evidence:** `scripts/krk_diagnostic.py` finds 0 dead strong-to-move states and 0 mismatches with the characterisation, in both orientations. This is supplementary only.
> - Local Lean (elan default `leanprover/lean4:v4.34.1`) is primary when Lean is run; no Lean is required this session. Push as `jfairfaxball-348` (repo-local Git Credential Manager config, `GCM_INTERACTIVE=never`).
>
> ## Objective
> A complete, hostilely audited paper proof of EC-C008(a), and hence (b). Plan the Lean statement for S018. Ledger unchanged.
>
> ## Facts to use (check each one)
> In a legal strong-to-move K+R vs K position:
> - the kings are not adjacent;
> - nobody is in check;
> - the strong side is never stalemated (the rook always has a legal move, and there are no pins);
> - castling, if the flags allow it, only adds strong-side moves, so a route that never castles is a valid series of legal moves.
>
> The lone king may currently be **shielded**: it stands on the rook's line, with the strong king between them.
>
> ## Required work
> 1. **Cooperative mating route** (both sides cooperate; every move legal). Starting plan (EC-C007 §6); refine it as needed:
>    - (i) by a symmetry of the board (justify each one), put the lone king in the a1 quadrant;
>    - (ii) the rook goes to h8 in ≤ 2 moves. It never gives check, because its new lines avoid that quadrant, and it never stands next to the lone king. If the strong king blocks the path, move it first;
>    - (iii) the lone king walks to {a1, b1} while the strong side passes. Strong passes by rook tempo h8↔g8 (the lone king stays on files ≤ f), or by strong-king moves away from the lone king's path;
>    - (iv) the strong king walks to a3 through ranks ≥ 3. Those squares are never adjacent to a1 or b1, so the lone king can shuffle a1↔b1 meanwhile;
>    - (v) fix the parity with a rook tempo;
>    - (vi) the rook mates along the first rank: Rh1# (or Rg1#).
>    At every lone-king turn, show that a **non-capturing** legal move exists (no stalemate, no forced capture en route), and that it is the one the route uses.
> 2. **Strategy simulator** `scripts/krk_route.py` + unit test. It plays the route deterministically from **every** strong-to-move legal state, in both orientations, checks every move against an independent legality generator, and confirms the route ends in checkmate. Use it to find failing cases while designing the route; report the maximum route length. It is supplementary, never the proof.
> 3. **Proof** `proofs/EC-C008_KRK_LIVE.md`, self-contained: definitions, one legality lemma per phase, complete case analysis of the obstacles (shielding, the strong king on the rook's path, the lone king near the rook, edge and corner squares, parity), and the derivation of (b) from (a) and EC-T0006.
> 4. **Audit** `audits/EC-C008_KRK_LIVE.md` (hostile): every phase, symmetries, flags, both orientations, the zero-length path, and the shielded cases.
> 5. **Status:** EC-C008 → `LOCAL_VERIFIED` only if no gap remains; otherwise stay `PROPOSED` and state the gap precisely. Record the planned Lean statement for S018: the route as a small number of move schemas, each with a `decide`-free legality lemma, and the main theorem `krk_strong_to_move_live` plus the characterisation `krk_dead_iff`.
>
> ## Closeout
> `sessions/S017_KRK_LIVE_PROOF.md` and a `sessions/SESSION_LEDGER.md` row: changes; proved / tested / conjectured; checks actually run; base and result SHAs; status; ledger effect (none). Install the next prompt in full: if Gate L passes, S018 = the Lean formalisation of EC-C008; otherwise a remedial S017 with the gap as its objective. Commit, push, merge to `main`.
