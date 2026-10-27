# Current work — KRK

**KRK OPEN.** Continue sustained research; KQK remains unselected. The [three major mathematical obligations](docs/KRK_COMPLETION.md) remain: all-history outcomes, FIDE correspondence, and exact global rule-aware distances. Lean is additional verification work, not a fourth mathematical obligation.

**Current obligation:** Finish six-ply weak destination geometry at the second edge file and near-corner edge file; then evaluate strong h=92/93 and weak h=91/92 with exact native history barriers. Lower clocks follow. The finite guard form in `KRKSixGeometry.lean` is an intermediate geometric description, not completion of the next band or class.

**Checked ongoing RAW outcomes:** [Strong h>=94](proofs/KRK_FIVE_PLY_HISTORY.md), with exact winning distances 1/3/5; [weak h>=93](proofs/KRK_SIX_PLY_HISTORY.md), with exact 2/4/6. Both colours, all board orientations and all admitted incoming histories; both-player holding on each complement. `KRKFivePlyHistory.lean` and `KRKSixPlyHistory.lean` are the main declarations.

**Latest geometric advance:** [Exact corner six-ply criterion](proofs/KRK_CORNER_SIX_GEOMETRY.md) now evaluates the twelve canonical strong-king points, with explicit rook inequalities, exact blockers, rook safety and legal-reply requirements. `KRKSixCorner.lean` handles mate separately and excludes stalemate. Near/second-edge geometry and native history barriers remain open. Full local build and axiom audit pass, 317 jobs.

**Latest outcome advance:** [Exact interior six-ply criterion](proofs/KRK_INWARD_CORNER_SIX_GEOMETRY.md): only two transposed king/rook families at each inward corner can force in six (clock-free, exact distance six). All other interior squares are excluded. `KRKSixInteriorHolding.lean` then proves full-history RAW drawing on strong h>=92 outside those four weak squares. `KRKFiveNear.lean` supplies the exact near-corner five-ply formula. Full local build and axiom audit pass, 316 jobs.

**Middle geometry:** [Compact middle/interior reductions](proofs/KRK_MIDDLE_FIVE_SIX_GEOMETRY.md): central edge weak six-ply boards are exactly the four-ply boards (clock-free only); an interior weak six-ply root must be one of four inward-corner squares. `KRKFiveMiddle.lean` removes all middle five-ply destination searches; `KRKSixMiddle.lean` and `KRKSixInterior.lean` give these restrictions. Full local build and axiom audit pass, 316 jobs.

**Earlier advance:** [Deeper castling geometry](proofs/KRK_DEEPER_CASTLING_GEOMETRY.md) checks the complete clock-free five-ply coordinate formula and proves actual castling cannot be a nonmating winning entry from strong h>=92. `KRKCastleSix.lean` uses inward-neighbour coverage, not a rights-clearing assumption. The full next-band outcome is still open.

**Useful entry points:** `KRKFourSlots.lean` gives seventeen four-ply destination points/regions. `KRKFiveWeakPrefix.lean` retains both first-prefix key indicators in the original trace. `KRKThreePlyExact.lean`, `KRKFourPlyExact.lean` and `KRKDistanceParity.lean` verify shorter-distance exclusions. Full local build and public axiom audit pass, 316 jobs. New results are unfrozen.

**Remaining scope:** Lower clocks, complete terminal/capture coverage, FIDE correspondence and global WDL/DTZ. The [static barrier reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) remains paper-only. Preserve all historical frozen sources/manifests and the [ledger](theorems/LEDGER.csv).
