# Current work — KRK

**KRK OPEN.** Continue the owner-authorised sustained research run without session ceremonies. KQK remains unselected.

**Objective:** A compact, explicitly evaluated outcome/strategy criterion for every admitted KRK history with positive halfmove clock, both turns and colours, legal terminal cases and current/intended claims, followed by full FIDE correspondence and exact global WDL/DTZ semantics. Supporting lemmas and generic recurrences do not complete this objective.

**Current obligation:** Extend the checked late-clock formulas to the remaining actual board orientations, retaining native `play` and original trace keys. Then address strong h=94/95 and lower clocks. Geometric symmetry does not by itself transport a RAW history or its castling rights. The nonmating h>=96 strong entries are ordinary king/rook moves; actual castling alternatives are excluded by the checked three-ply theorem.

**Checked weak h>=95 bands, both strong colours:** Every ongoing history on bottom-edge files zero through four is now evaluated, with exact winning distances two/four and both-player holding on the complement:

- [Corner W=(0,0)](proofs/KRK_CORNER_WEAK_HISTORY.md): three finite neighbour guards plus horizontal/vertical original-trace slot tests.
- [Near-corner W=(1,0)](proofs/KRK_NEAR_WEAK_HISTORY.md): five guards, excluding the two inward replies, plus corner/second-file/vertical slot tests.
- [W=(2,0)](proofs/KRK_SECOND_WEAK_HISTORY.md): both opposition replies, including the extra west king entry.
- [W=(3,0),(4,0)](proofs/KRK_CENTRAL_WEAK_HISTORY.md): branch-specific rook intervals.

**Strong child formulas:** [Horizontal near-corner](proofs/KRK_NEAR_CORNER_FULL_THREE_PLY_HISTORY.md), [corner](proofs/KRK_CORNER_FULL_THREE_PLY_HISTORY.md), [vertical near-corner](proofs/KRK_VERTICAL_NEAR_CORNER_THREE_PLY_HISTORY.md), and the second-file table in [the near-corner weak proof](proofs/KRK_NEAR_WEAK_HISTORY.md) evaluate entire strong h>=96 regions with finite king points/rook intervals or rays, and exact one/three-ply distances. No future-outcome predicate remains in those tests.

**Reusable proof entry points:** `KRKWeakPrefixEntry.lean` proves that a first quiet weak append contributes zero to both later last-reply barrier queries. `KRKSlotPrefix.lean`, `KRKSecondSlotPrefix.lean`, and `KRKCornerSlotPrefix.lean` express complete child formulas in the original weak trace. `KRKWeakBranch.lean` verifies child ongoing/admission and uniform three-ply certificates. These allow finite coordinate guards to combine all weak choices without rebuilding history updates per family.

**Remaining global gap:** The [fixed incoming-key barrier reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) still lacks a complete geometric evaluation and matching defender lower bounds over all positive clocks. The checked deadline is max(1,100-h) on strong turns and 100-h on weak turns. Reflected/rotated actual histories, lower clocks, legal terminal/capture boundaries, full FIDE-rule correspondence and global distances remain unfinished.

**Trust boundary:** New results are locally Lean-checked and unfrozen. Preserve the 48 historical frozen bundles and immutable evidence in [the ledger](theorems/LEDGER.csv). Follow AGENTS.md mathematical integrity requirements; commit coherent checked work and continue. No new session reports or freeze ceremony are required.
