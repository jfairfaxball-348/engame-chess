# Lean 4 formal proofs

Pinned, core-only Lean 4 project (no mathlib, no dependencies).

- Toolchain: `lean-toolchain` = `leanprover/lean4:v4.35.0` (S020 migration; v4.34.1 before; Palomar minimum v4.35.0-rc2)
- Build: `cd formal && lake build`
- Axiom report: `cd formal && lake env lean AxiomCheck.lean`
- Layout: one module per theorem; shared definitions in their own modules. Frozen theorem modules are never edited.
- CI builds incrementally from a cached `.lake` and only on `formal/**` changes. It re-checks only changed modules and their importers. See `docs/PROOF_PROTOCOL.md`, "Re-checking obligations".

| Candidate | File | Main declaration | Audit |
|---|---|---|---|
| EC-C001 / **EC-T0001 (frozen)** (K vs K dead) | `EndgameChess/KK.lean` | `EndgameChess.KK.dead_of_admissible` | [audits/EC-C001_KK_LEAN.md](../audits/EC-C001_KK_LEAN.md) |
| EC-C002 / **EC-T0002 (frozen)** (K+B vs K dead) | `EndgameChess/KBK.lean` (imports `KK`) | `EndgameChess.KBK.dead_of_LKBK` | [audits/EC-C002_KBK_LEAN.md](../audits/EC-C002_KBK_LEAN.md) |
| EC-C004 K1 (rules kernel) | `EndgameChess/Rules/{Board,Position,Moves,Sanity}.lean` | `EndgameChess.Rules.Legal`, `mem_legalPositions`, `initial_legal_count` | [audits/EC-C004_K1.md](../audits/EC-C004_K1.md); bridge [docs/RULES_KERNEL.md](../docs/RULES_KERNEL.md) |
| EC-C004 K3 / EC-C005, EC-C006 = **EC-T0003, EC-T0004 (frozen)** | `EndgameChess/Rules/{Flags,Reach,Outcome}.lean` | `dead_of_legal_into_KK`, `dead_of_legal_into_KBK`, `arisen_KK_dead`, `arisen_KBK_dead`, `Rule5_2_2` | [audits/EC-C004_K3.md](../audits/EC-C004_K3.md) |
| EC-C003 / **EC-T0005 (frozen)** (K+N vs K dead, over the kernel) | `EndgameChess/Rules/KNK.lean` (imports `Rules.Outcome`) | `dead_of_legal_into_KNK`, `arisen_KNK_dead`, `knk_drawn_by_rule` | [audits/EC-C003_KNK_LEAN.md](../audits/EC-C003_KNK_LEAN.md) |
| EC-C007 / **EC-T0006 (frozen)** (dead K+R vs K: forced capture / stalemate) | `EndgameChess/Rules/KRK.lean` (imports `Rules.KNK`) | `krk_dead_of_forced_capture`, `dead_of_succ_KK`, `krk_forced_capture_drawn_by_rule` | [audits/EC-C007_KRK_DEAD_LEAN.md](../audits/EC-C007_KRK_DEAD_LEAN.md) |
| EC-C008 part 1 (live K+R vs K; S021, partial, not frozen) | `EndgameChess/Rules/KRKLive/{Basic,Endgame}.lean` (imports `Rules.KRK`) | `not_deadK_of_winM`, `winM_of_sym`, `krk_lemmaM`, `krk_lemmaE`, `rect_minus_box_conn`, `krk_lemmaW`, `krk_lemmaS`, `krk_settled_live` | [audits/EC-C008_KRK_LIVE_LEAN.md](../audits/EC-C008_KRK_LIVE_LEAN.md) |
| EC-C004 K2 (agreement) | `EndgameChess/Rules/{Lemmas,AgreeKK,AgreeKBK}.lean` | `legal_ofKK_iff`, `legal_ofKBK_iff`, `kernel_dead_KK`, `kernel_dead_KBK` | [audits/EC-C004_K2.md](../audits/EC-C004_K2.md) |

`Checks/` holds evaluation-only files (e.g. `Checks/Perft.lean`, run with `lake env lean Checks/Perft.lean`). They contain no theorems.

Lean checks the mathematical model only. The correspondence between the model and the FIDE 2023 Laws (assumption A1, lemma L3a, Article 5.2.2) is the prose bridge in `proofs/EC-C001_KK.md`. A successful build is not a ledger freeze: see `docs/PROOF_PROTOCOL.md`, Gate Z.
