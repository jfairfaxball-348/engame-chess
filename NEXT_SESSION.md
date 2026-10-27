# Current work — KRK

**KRK OPEN.** Continue the owner-authorised sustained research run without session ceremonies. KQK remains unselected.

**Objective:** A compact, explicitly evaluated outcome/strategy criterion for every admitted KRK history with positive halfmove clock, both turns and colours, legal terminal cases and current/intended claims, followed by full FIDE correspondence and exact global WDL/DTZ semantics. Supporting lemmas and generic recurrences do not complete this objective.

**Current obligation:** Finish the late-clock edge history band at W=(1,0) and W=(0,0), weak h>=95, using the checked four-ply geometry and the original incoming trace. Then address reflected actual histories, strong h=94/95 and lower clocks. Preserve actual flags; geometric board symmetry does not automatically transport a RAW history.

**Latest checked outcome:** [W=(2,0) weak h>=95](proofs/KRK_SECOND_WEAK_HISTORY.md) is completely evaluated in RAW, for either strong colour, with exact winning distances two/four and both-player holding on the complement. Its opposition branch requires separate tests for both weak replies. After the west reply, either a rook interval or the extra fixed king entry may clear the original-history barriers. All counts use the root trace. Source: `KRKSecondWeakBand.lean`, `KRKSecondOppositionHistory.lean`, `KRKSecondWestHistory.lean`, `KRKSecondOppositionPrefix.lean`.

**Current method:** The [full near-corner strong formula](proofs/KRK_NEAR_CORNER_FULL_THREE_PLY_HISTORY.md) now evaluates every strong W=(1,0), h>=96 history using three king points and three explicit rook intervals, with exact distance one/three. `KRKWeakPrefixEntry.lean` transports any actual last-reply entry through an initial weak move back to its original trace. Extend the finite slot formulas to the corner and transposed near-corner, then combine the weak root replies; avoid rebuilding separate key-update proofs for each family.

**Useful checked inputs:** [central weak history](proofs/KRK_CENTRAL_WEAK_HISTORY.md), [near-corner three-ply history branch](proofs/KRK_NEAR_CORNER_HISTORY_BRANCH.md), [near-corner four-ply geometry](proofs/KRK_NEAR_CORNER_FOUR_PLY.md), [corner four-ply geometry](proofs/KRK_CORNER_FOUR_PLY.md), [interior escape/lower bound](proofs/KRK_INTERIOR_LOWER_BOUND.md), and [three-ply incoming-key barriers](proofs/KRK_THREE_PLY_BARRIERS.md). The corner necessity proof requires nonempty replies: three rook-(1,1) traps otherwise satisfy a universal reply condition vacuously.

**Remaining global gap:** The [fixed incoming-key barrier reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) still lacks a complete geometric evaluation and matching defender lower bounds. The checked deadline is max(1,100-h) on strong turns and 100-h on weak turns. Full-history low-clock outcomes, terminal/capture boundaries, FIDE-rule correspondence and global distances remain open.

**Trust boundary:** The new results are locally Lean-checked and unfrozen. Preserve the 48 historical frozen bundles and immutable evidence in [the ledger](theorems/LEDGER.csv). Follow the mathematical integrity requirements in AGENTS.md; commit coherent checked work and continue. No new session reports or freeze ceremony are required.
