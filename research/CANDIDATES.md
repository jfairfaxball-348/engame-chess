# Candidate theorem register

This file contains **not-yet-frozen research claims**. Only `theorems/LEDGER.csv` is the frozen-theorem register.

| ID | Candidate | Status | Required local evidence | Notes |
|---|---|---|---|---|
| EC-C001 | Every KK-admissible, game-arisen position is dead and therefore a FIDE draw | FORMAL_VERIFIED (S002, 2026-10-16) | [Proof](../proofs/EC-C001_KK.md) + [audit](../audits/EC-C001_KK.md) + `scripts/kk_diagnostic.py` (supplement); Lean `formal/EndgameChess/KK.lean` + [Lean audit](../audits/EC-C001_KK_LEAN.md) | Rule edition FIDE 2023; assumption A1 ("adjoining" = Chebyshev neighbour). Lean: `EndgameChess.KK.dead_of_admissible` (also `admissible_of_last_move_legal`, `dead_of_last_move_legal`); toolchain `leanprover/lean4:v4.34.1`, core only; proof-source commit `342be5aefe16a9c5c882aab4f118a21472235fc3`; axioms `[propext, Classical.choice, Quot.sound]`. Prose bridge (A1, L3a, general L0, 5.2.2) not machine-checked. Audits same-session. **Frozen as [EC-T0001](../theorems/frozen/EC-T0001/v1.md) in S003** (ledger row in `theorems/LEDGER.csv`). [superseded draft](KK_DRAFT.md) |
| EC-C002 | Every legal K+B vs K game-arisen position is dead | PROPOSED | Complete bishop attack/move and possible-mate exclusion proof | Do not assume a check is impossible |
| EC-C003 | Every legal K+N vs K game-arisen position is dead | PROPOSED | Complete knight attack/move and possible-mate exclusion proof | Do not assume a check is impossible |

Possible future IDs `EC-C004` onwards only after selecting a genuinely well-posed next claim. Candidate statuses: `PROPOSED`, `LOCAL_VERIFIED`, `FORMAL_VERIFIED`, `REJECTED`. Do not mark as `FROZEN` here until an actual ledger entry and manifest exist.
