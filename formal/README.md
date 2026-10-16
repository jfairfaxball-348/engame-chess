# Lean 4 formal proofs

Pinned, core-only Lean 4 project (no mathlib, no dependencies).

- Toolchain: `lean-toolchain` = `leanprover/lean4:v4.34.1`
- Build: `cd formal && lake build`
- Axiom report: `cd formal && lake env lean AxiomCheck.lean`

| Candidate | File | Main declaration | Audit |
|---|---|---|---|
| EC-C001 (K vs K dead) | `EndgameChess/KK.lean` | `EndgameChess.KK.dead_of_admissible` | [audits/EC-C001_KK_LEAN.md](../audits/EC-C001_KK_LEAN.md) |

Lean checks the mathematical model only. The correspondence between the model and the FIDE 2023 Laws (assumption A1, lemma L3a, Article 5.2.2) is the prose bridge in `proofs/EC-C001_KK.md`. A successful build is not a ledger freeze: see `docs/PROOF_PROTOCOL.md`, Gate Z.
