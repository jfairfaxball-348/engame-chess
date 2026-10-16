# NEXT SESSION — S006: Freeze EC-C002 as EC-T0002 (Gate Z), then open the rules-kernel track

**Owner instruction:** Execute this S006 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C002 is `FORMAL_VERIFIED` (S005). Do not treat this prompt as evidence that a freeze has happened.

## Owner decision (recorded 2026-10-16)
The trust boundary of EC-T0001/EC-T0002 has three prose-only items. The owner wants them addressed:
- **(G1)** each theorem's bespoke move relation (`LegalKK`, `KBK.Step`) is trusted to equal the FIDE-legal moves;
- **(G2)** "arisen" positions reached by a capture from larger material are covered only in prose;
- **(G3)** the Article 5.2.2 "immediate draw" step is prose.

**Agreed order:**
1. S006 freezes EC-C002 now, with its boundary stated honestly.
2. S007–S009 build a single general **rules kernel** in Lean that closes G1 and G2 and makes G3 an explicit named rule.
3. v2 manifests then re-anchor EC-T0001 and EC-T0002 on the kernel.
4. EC-C003 (K+N vs K) waits until the kernel exists, so that it is built on the kernel from the start.

## Part A — Freeze EC-T0002 (Gate Z)
Freeze EC-C002 as **EC-T0002** per `docs/PROOF_PROTOCOL.md` Gate Z, citing the S005 proof-source commit **`15610256c9588e2bb5e0c19b035bbfd4437b2e31`**. Use `theorems/frozen/EC-T0001/v1.md` as the template. Do not change any mathematics or Lean source.

1. **Re-verify only this theorem's obligation.** In a fresh clone at `15610256c9588e2bb5e0c19b035bbfd4437b2e31`, using `leanprover/lean4:v4.34.1`, run:
   - `cd formal && lake build`;
   - `lake env lean AxiomCheck.lean` — every `EndgameChess.KBK.*` line must be a subset of `[propext, Classical.choice, Quot.sound]` or say "does not depend on any axioms";
   - the forbidden-token grep.

   Check the SHA-256 hashes: `KBK.lean` must be `c668e0c044cf17caa74ad8a75cfdeb0b758e3ccd5b0956ffde88cec2c895c6d7` and `KK.lean` must be `4843459ca26af93e15e5894a9f32183d46f8c554132e81051c1c21140509b1a0`. On any mismatch, stop: do not freeze, and install a remedial prompt.
2. **Drift check.** `git diff 15610256 HEAD -- formal/EndgameChess/` must be empty.
3. **CI evidence.** Record `Lean build (EC formal proofs)` run **38907468354** on the proof commit (conclusion success, observed in S005). Re-confirm it with the GitHub tools.
4. **Manifest** `theorems/frozen/EC-T0002/v1.md`. Use the same sections as EC-T0001, and save the build and axiom logs beside it. It must contain:
   - the statement and scope: both orientations; FIDE 2023 Arts 1.2, 1.4.1, 3.1–3.2, 3.5, 3.8–3.10, 5.2.2;
   - the verbatim `#check` output for `dead_of_LKBK` and `dead_of_step`;
   - its dependency on EC-T0001 (`admissible_of_legal_step`, `not_inCheck_of_admissible`);
   - the trust boundary, listing:
     - A1;
     - the reading of 3.1.2 + 3.2 + 3.5 as the bishop attack;
     - **G1, G2 and G3**, explicitly marked *"scheduled for closure by the rules-kernel track (S007–S009); a v2 manifest will supersede this boundary"*;
     - that the audits were done in the same session;
   - the line "classical, no novelty".
5. **Ledger.** Append the `EC-T0002` row with Python `csv` and `lineterminator="\n"` (LF only):
   - `proof_commit_sha=15610256c9588e2bb5e0c19b035bbfd4437b2e31`
   - `lean_file=formal/EndgameChess/KBK.lean`
   - `lean_declaration=EndgameChess.KBK.dead_of_LKBK`
   - `local_proof_path=proofs/EC-C002_KBK.md`

   Then `python3 scripts/validate_ledger.py` must print `2 frozen theorem(s)`, and the unit tests must pass.
6. **Status files.**
   - `research/CANDIDATES.md`: note that EC-C002 is frozen as EC-T0002.
   - `theorems/README.md`: frozen count → 2.
   - Also update `README.md`, `formal/README.md` and `docs/ROADMAP.md`.

## Part B — Record the kernel track (documentation only, no Lean in S006)
Edit `docs/ROADMAP.md`: add a **Rung K (rules kernel)** above rung 3, describing S007–S009 as below and marking EC-C003 as deferred until K2. Add a `research/CANDIDATES.md` entry **EC-C004**: *"General FIDE 2023 Article 3 legal-move kernel agrees with `LegalKK` and `KBK.Step` on their material classes"*, status `PROPOSED`.

## Closeout
Write `sessions/S006_FREEZE_EC-T0002.md` and add a `sessions/SESSION_LEDGER.md` row. Record:
- the checks that were actually run;
- the base SHA and the proof SHA;
- the CI evidence;
- the ledger effect (+1, giving 2 frozen theorems).

Install **S007** in `NEXT_SESSION.md` and include it **in full** in the closeout. Then commit, push and merge to `main`.

### S007 specification (expand into the full prompt)
**S007 — Rules kernel K1: general position and Article 3 move model (Gate L + Lean definitions).**
- **New modules** (KK.lean and KBK.lean are frozen and must not be edited):
  - `formal/EndgameChess/Rules/Board.lean`: squares, colours, piece types. It may re-export `EndgameChess.KK.Square`/`Colour`, or define its own and prove the two equivalent.
  - `formal/EndgameChess/Rules/Position.lean`: a piece placement as a partial map from square to (colour, type), plus side to move, castling rights and an en-passant target.
  - `formal/EndgameChess/Rules/Moves.lean`: a legal-move relation written clause by clause from FIDE 2023 Articles 3.1–3.10:
    - pseudo-moves for each piece (3.2–3.8), with obstruction for sliding pieces (3.5);
    - pawn single and double advance, diagonal capture, en passant (3.7.3) and promotion (3.7.5);
    - castling with all of the 3.8.2 conditions;
    - the self-check filter (3.9.2);
    - attack defined via 3.1.2 and 3.1.3.

  Comment each clause with its Article number, quoting the rule text verbatim (retrieved from https://handbook.fide.com/chapter/E012023).
- **Prose spec** `docs/RULES_KERNEL.md`: a table mapping each Article sub-clause to the Lean clause that encodes it. This table is the single trusted bridge from FIDE to Lean, and is the place for a human second reader to review.
- **Sanity theorems** (no chess claims yet):
  - the initial position (Art. 2) is well formed;
  - White has exactly 20 legal moves from it, proved by kernel `decide` only if it is fast; otherwise by explicit enumeration with a proof;
  - both kings are never in check after a legal move.
- **Independent cross-check:** a Python perft-style count from the initial position to depth 3, written independently of the Lean code. The known perft values (20, 400, 8902) are public mathematics, not tablebase data; cite them and compare.
- **Do not prove the agreement theorems yet** (that is S008). Candidate EC-C004 stays `PROPOSED`.

**Later sessions (described in the S007 prompt's closeout, not executed):**
- **S008 — K2, agreement.** Prove that on K-vs-K positions the kernel relation is exactly `KK.LegalKK` (via embeddings both ways), and that on K+B vs K / K vs K positions it is exactly `KBK.Step`. **This closes G1** for both theorems.
- **S009 — K3, reachability and rules.**
  - Define `Arisen` as reachable from the initial position by kernel-legal moves.
  - Prove that every kernel-legal move producing K vs K or K+B vs K material yields `Admissible` / `LKBK`, whatever the predecessor. **This closes G2.**
  - Define `DeadPosition` over the kernel. Encode Art. 5.2.2 as an explicit named definition `Rules.Outcome` (*dead ⇒ drawn immediately*), clearly labelled as a *rule encoding, not a theorem*, and derive the draw corollaries. **This makes G3 explicit.**
  - Then issue `v2.md` manifests for EC-T0001 and EC-T0002, with superseding ledger rows per the protocol, citing the kernel commits. The v1 records stay unchanged.
- **After S009:** EC-C003 (K+N vs K), Gate L then Lean, stated directly over the kernel.
