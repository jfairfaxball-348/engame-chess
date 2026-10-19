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
| EC-C008 / **EC-T0007 (frozen S023)** (complete K+R vs K L1; Lean S021–S022) | `EndgameChess/Rules/KRKLive/{Basic,Endgame,Reply,Relocation,Main}.lean` (imports `Rules.KRK`) | `krk_strong_to_move_live`, `krk_dead_iff`, `arisen_krk_strong_live`, `krk_drawn_by_rule_iff` (route: `krk_P1`, `krk_RLh`, `krk_RLf`, `krk_lemmaS`…`krk_lemmaM`) | [audits/EC-C008_KRK_LIVE_LEAN.md](../audits/EC-C008_KRK_LIVE_LEAN.md) |
| EC-C004 K2 (agreement) | `EndgameChess/Rules/{Lemmas,AgreeKK,AgreeKBK}.lean` | `legal_ofKK_iff`, `legal_ofKBK_iff`, `kernel_dead_KK`, `kernel_dead_KBK` | [audits/EC-C004_K2.md](../audits/EC-C004_K2.md) |

`Checks/` holds evaluation-only files (e.g. `Checks/Perft.lean`, run with `lake env lean Checks/Perft.lean`). They contain no theorems.

Lean checks the mathematical model only. The correspondence between the model and the FIDE 2023 Laws (assumption A1, lemma L3a, Article 5.2.2) is the prose bridge in `proofs/EC-C001_KK.md`. A successful build is not a ledger freeze: see `docs/PROOF_PROTOCOL.md`, Gate Z.

## S024 forcing prerequisites (frozen S025 as EC-T0008/0009)

Proof-source: `fca2ca88c8391b1d2bd49c3db9f2fa04258a4a87`; [audit](../audits/EC-C009_C010_LEAN.md), [fresh verification](../sessions/evidence/S024/README.md).

| Candidate | New modules | Main declarations |
|---|---|---|
| EC-C009 / **EC-T0008 (frozen)** | `Rules/ForcingDefinitions.lean`, `Rules/ForceMate.lean` | `mateWithin_sound`, `forceMate_not_dead`, `forceMate_no_moves_iff`, `dead_reply_not_forceMate`, `forceMate_choose`, `forceMate_defend` |
| EC-C010 / **EC-T0009 (frozen)** | `Rules/KRKConfinement.lean` | `krk_protected_reply`, `rook_rank_barrier`, `krk_protected_rank_reply`, `protected_rank_raise_unprotected` |
| Fixed witnesses | `Rules/KRKForcingExamples.lean` | optional-capture live-but-not-forcing, one-/zero-ply mate, protected-rank stalemate, blocked-ray crossing |

The new game predicate uses a uniform finite ply bound and omits clocks/repetition. The protected barrier is a reply invariant; it does not supply a complete advancing strategy. EC-C011 has no completed forcing proof or Lean flagship.

Freeze manifests: [EC-T0008](../theorems/frozen/EC-T0008/v1.md) and [EC-T0009](../theorems/frozen/EC-T0009/v1.md). Primary proof/definition modules are now immutable; new safety/progress lemmas must use new modules. S025 changed no Lean source.

## S026 safety and checking progress (frozen S027 as EC-T0010/0011)

Proof-source `e8daef6daee088c3adaf1c21b51c0a8f1e31103d`; [audit](../audits/EC-C012_C013_LEAN.md), [fresh verification](../sessions/evidence/S026/README.md).

| Candidate | New source | Main result |
|---|---|---|
| EC-C012 | `Rules/KRKForcing/Safety.lean` | `krk_safe_reply`, `krk_safe_rank_reply`, `krk_safe_weak_live`: capture safety from distance or protection, every kernel reply covered |
| EC-C013 | `Rules/KRKForcing/CheckProgress.lean` | `krk_opposition_four_ply`: chosen check, every reply, king-up, every reply; strict rank progress and distant barrier, or edge mate; `krk_opposition_edge_force` |
| Fixed controls | `Rules/KRKForcing/Examples.lean` | edge forcing, failed two-/three-file margins, a successful phase not restoring opposition |

No frozen module was edited. The general KRK forcing proof remains incomplete; these statements cover an exact geometric entry family, both colours and arbitrary flags.

S027 Gate Z froze the three-declaration safety bundle as [EC-T0010](../theorems/frozen/EC-T0010/v1.md) and the ten-declaration checking-phase bundle as [EC-T0011](../theorems/frozen/EC-T0011/v1.md). Exact-source clean build, 197 standard-axiom-subset reports, and all 17 S026 declaration checks passed; [new evidence](../theorems/frozen/VERIFICATION-S027/README.md). `Safety.lean` and `CheckProgress.lean` are now immutable. The phase needs strong turn, same-file kings two ranks apart, a four-file rook margin and rook off the lone king's rank, for either colour and arbitrary flags. No general KRK forcing, clock/repetition or initial-position result is claimed; setup/re-entry remains open.

## S028 image bounds and bounded upper-band contraction (FORMAL_VERIFIED, not frozen)

Proof source: `cb5d3bb713257d7cac8e3c1f9d82d8e77b746d6c`; [paper image proof](../proofs/EC-C014_KRK_PHASE_IMAGE.md), [rank/rescue proof](../proofs/EC-C015_KRK_RANK_ADVANCE.md), [fidelity audit](../audits/EC-C014_C015_LEAN.md), [new exact-source evidence](../sessions/evidence/S028/README.md).

| Candidate | New modules | Main declarations |
|---|---|---|
| EC-C014 | `KRKForcing/PhaseImage.lean` | `krk_follow_check_image`, `krk_opposition_phase_image`: actual two-reply image with legal ancestry and all-defences quantifiers |
| EC-C015 | `KRKForcing/RankAdvance.lean`, `RookRescue.lean`, `RankAdvanceRescue.lean` | `krk_rank_advance`, `krk_barrier_rook_rescue`, `krk_rank_advance_rescue`, `krk_phase_image_upper_advance`: two-or-four-ply rank contraction covering the entire upper band |
| Fixed controls | `KRKForcing/ReentryExamples.lean` | actual chase cycle, protected-rook stalemate, lower-band wall crossing, hanging raised rook with legal rescue |

All fifteen new theorem declarations are included in `AxiomCheck.lean`. Frozen modules remain unchanged. The rank phase has explicit nonempty replies and a decreasing barrier-rank potential; it does not preserve PhaseImage or establish a full repeated strategy. Non-aligned lower-band pursuit/tempo, post-contraction normalization and arbitrary-arrival setup remain open. EC-C011 remains PROPOSED. No clock/repetition or initial-position result is asserted.
