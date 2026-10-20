# NEXT SESSION — S058: Exact raw threshold exclusion characterization

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Fetch ALL remote heads, merge prior unmerged work, latest main,
existing checkout. Commit/push branch, merge/push main, compare remote identities;
never force main. FULL stable progress table, Syzygy last, immediate session delta.

## Starting point

S057 froze EC-C034 as EC-T0032, OWN proof-source
1f262968c80a1352c156f6e0c07dd5132c432b13; 32 frozen bundles, not solved classes.
Read manifest/Gate Z evidence, S056/57 closeouts, paper/audits, RawClaims complete
definitions/certificate, frozen current count append/clock append definitions,
S032 specification, charter/protocol/roadmap/candidates.

## Principal task

Exact standalone paper and separate adversarial audit BEFORE Lean, then register
EC-C035 LOCAL_VERIFIED only after complete local argument. ONE NEW main theorem
module RawClaims/ExclusionCharacterization, no extra definitions needed:
for EVERY raw state s,
 ¬AvailableThreshold s ↔
 RawClock.clock s.trace <100 ∧
 RawRepetition.currentOccurrences s <3 ∧
 (∀m,∀hm:isLegal(erase s)m=true,
   RawClock.clock (append s m hm).trace <100 ∧
   RawRepetition.occurrences s.trace (play(erase s)m) <2).

Use exact frozen raw threshold definitions, every actual legal append and frozen
append_currentOccurrences. Forward: exclude root and each intended child;
childcount=queriedcount+1<3 iff queriedcount<2. Reverse: root and every child below
threshold, refute disjunction/existential. This is an IFF, not the sufficient
rootclock+1 budget of EC-T0032. It keeps actual childclock: zeroing child can be
safe despite large root clock; root itself still checked separately. Never
substitute old current key for new endpoint query, drop an adverse intended
move or assume raw illegal play equality. All flags/colours/promotions/stored
traces/hm retained. No-reply universal vacuous but root conditions required.
Audit boundaries99/100,2/3, child old-query1/2, zeroing and pseudo-only cases.
Same-agent review, not independent external audit; symbolic controls, no concrete
full-game diagnostic, enumeration/engine/tablebase/certificates or novelty.

Raw bookkeeping ONLY: not FIDE CanClaim correctness, no full key/rights-history
identity, no-earlier-terminal admissibility, real claims/automatic draws/mate
precedence, complete Layer, strategy lifting, numerical KRK, holding/outcome,
WDL/DTZ/Syzygy or initial-position result. Do not alter frozen sources/definitions.

## Verification and closeout

Aggregates additive, incremental changed module/importers plus COMPLETE working
runner. Publish proof source BEFORE ONE NEW GitHub Gate F clone at FULL exact SHA,
.lake absent before full build then COMPLETE AxiomCheck; inspect exact main and
standard-three subsets. Retain full logs/commands/exits/times/UTC/toolchain/
executable, all source/transitive SHA256, clean HEAD/tree/status; compare full
working/clean output and formal bytes. Official core Lean4.35.0, no dependency/shim.
One fresh build at a time; interruptions/retries honestly retained. Gate Z separate,
no frozen manifest/ledger row in S058. Preserve all prior protected files/32 rows.
Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff checks,
no unrelated diagnostics/trivial tests. Hosted CI unobserved unless inspected.

Update candidate/roadmap/README/session ledger/progress; write
sessions/S058_EXACT_RAW_THRESHOLD_EXCLUSION.md with actual evidence and FULL
installed S059 prompt (consider own-source freeze). Commit/push/merge/push,
compare remotes; continue until owner stops. Record any gap honestly.

Use available runtime guidance/status/network policy, inherited proxy/CA,
ELAN_HOME=/workspace/.tools/elan. Lake in formal/, Python root; official core
Lean4.35.0, TLS/checksums unchanged.
