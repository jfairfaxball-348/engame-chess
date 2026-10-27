# Current work — KRK

**KRK OPEN.** Continue sustained research; KQK remains unselected. The [three major mathematical obligations](docs/KRK_COMPLETION.md) remain: all-history outcomes, FIDE correspondence, and exact global rule-aware distances. Lean is additional verification work, not a fourth mathematical obligation.

**Current obligation:** Derive compact six-ply weak destination points/rook regions, then evaluate strong h=92/93 and weak h=91/92 with the exact native history barriers. Lower clocks follow. The finite guard form in `KRKSixGeometry.lean` is an intermediate geometric description, not completion of the next band or class.

**Checked ongoing RAW outcomes:** [Strong h>=94](proofs/KRK_FIVE_PLY_HISTORY.md), with exact winning distances 1/3/5; [weak h>=93](proofs/KRK_SIX_PLY_HISTORY.md), with exact 2/4/6. Both colours, all board orientations and all admitted incoming histories; both-player holding on each complement. `KRKFivePlyHistory.lean` and `KRKSixPlyHistory.lean` are the main declarations.

**Latest advance:** [Deeper castling geometry](proofs/KRK_DEEPER_CASTLING_GEOMETRY.md) checks the complete clock-free five-ply coordinate formula and proves actual castling cannot be a nonmating winning entry from strong h>=92. `KRKCastleSix.lean` uses inward-neighbour coverage, not a rights-clearing assumption. The full next-band outcome is still open.

**Useful entry points:** `KRKFourSlots.lean` gives seventeen four-ply destination points/regions. `KRKFiveWeakPrefix.lean` retains both first-prefix key indicators in the original trace. `KRKThreePlyExact.lean`, `KRKFourPlyExact.lean` and `KRKDistanceParity.lean` verify shorter-distance exclusions. Full local build and public axiom audit pass, 310 jobs. New results are unfrozen.

**Remaining scope:** Lower clocks, complete terminal/capture coverage, FIDE correspondence and global WDL/DTZ. The [static barrier reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) remains paper-only. Preserve all historical frozen sources/manifests and the [ledger](theorems/LEDGER.csv).
