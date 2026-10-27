# Current work — KRK

**KRK OPEN.** Continue sustained research; KQK remains unselected.

**Objective:** An explicitly evaluated outcome/strategy criterion for every admitted KRK positive-clock history, both turns/colours, terminal/capture/current/intended-claim cases, followed by full FIDE correspondence and exact global WDL/DTZ. Generic recurrences or supporting lemmas do not complete it.

**Current obligation:** Weak h=93/94, then strong h<=93 and lower clocks. The [complete strong h>=94 formula](proofs/KRK_FIVE_PLY_HISTORY.md) now supplies exact 1/3/5-ply winning distances and both-player holding on its complement. The [all-orientation late-clock formulas](proofs/KRK_GLOBAL_LATE_CLOCK_HISTORY.md) now cover every ongoing RAW strong h>=96 and weak h>=95 position, with exact minimum winning bounds 1/3 and 2/4 respectively, and both-player holding on the complement. All incoming traces and native flags are retained.

**New entry points:** `KRKFourSlots.lean` gives the exhaustive seventeen-point four-ply destination catalogue. `KRKCastleFour.lean` excludes castling entries. `KRKStrongPrefix.lean` retains every first-append key indicator in the original trace. `KRKFivePlyHistory.lean` proves the complete strong h>=94 outcome; `KRKThreePlyExact.lean` and `KRKDistanceParity.lean` give matching minimum-distance bounds. Aggregate build and axiom audit pass, 304 jobs.

**Earlier entry points:** `KRKCanonicalSlots.lean` gives seven exhaustive canonical last-reply slots. `KRKNativeFrame.lean` normalizes coordinates only. `KRKFramedHistory.lean` evaluates the global strong band; `KRKFramedPrefix.lean` lifts its point/ray tests into the original weak trace; `KRKGlobalWeakBand.lean` evaluates all weak neighbours. Aggregate Lean build and public axiom audit pass locally. These modules are unfrozen.

**Remaining gap:** Evaluate deeper fixed incoming-key barriers with matching lower bounds against every strong alternative, preserving actual castling and trace keys. The [static reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) remains paper-only. Lower clocks, full terminal/capture coverage, FIDE correspondence and global distances remain unfinished. Preserve the 48 historical frozen bundles and [ledger](theorems/LEDGER.csv).
