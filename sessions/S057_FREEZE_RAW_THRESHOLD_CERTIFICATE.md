# S057 — Freeze raw threshold exclusion certificate

2026-10-20, base main e475d700baafa5b9ed71a2a7b23be3c7f71a745c,
branch session/s057-freeze-raw-threshold-certificate. Explicit all-heads fetch,
no prior unmerged work, existing checkout; owner authorises consecutive sessions
and publication. EC-C034 frozen as EC-T0032; 32 bundles, no class coverage upgrade.

## Exact result and fidelity

For every raw state s, explicit root clock+1<100, root currentcount<3 and
EVERY actual legal intended new-key OLD-history query<2 imply no raw
AvailableThreshold. CurrentThreshold is root clock>=100 OR currentcount>=3;
IntendedThreshold existentially quantifies every actual legal append with a child
CurrentThreshold. Root arithmetic and frozen actual clock/count append laws
exclude both root and every child threshold. All indexed traces/hm/colours/flags/
promotions retained, no terminal/material/history/strategy restriction.
Raw predicates NOT certified FIDE CanClaim/adjudication; frozen Layer unchanged.

Both complete modules frozen unchanged; paper/Lean/evidence fidelity reviewed.
[Review](../theorems/frozen/VERIFICATION-S057/fidelity-review.md).

No full FIDE key/Article9.2.3/rights-history identity, repetition threshold/claim,
no-earlier-terminal histories, automatic-draw/mate precedence adjudication,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial value.
Same-agent review, not independent external audit. Symbolic threshold99/100,2/3/zeroing/no-reply/pseudo-only controls,
not a compatible actual chess-game run. No enumeration/oracle/stored certificate,
executable hash/search or novelty claim.

## Observed verification and publication

Own source `1f262968c80a1352c156f6e0c07dd5132c432b13`; NEW GitHub clone `/tmp/engame-s057-gate-z`, no .lake before build. Full 83-job build exit 0 in 488.012s; COMPLETE AxiomCheck exit 0 at 2026-10-20T13:26:42Z; 281 allowed reports. Main standard-three; whole report identical to S056 Gate F.

Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status and full logs/commands/exits/times/UTC/toolchain
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Hosted CI unobserved. One new successful
clean run, no failure/repeated build; no source edit/incremental build. Relevant
ledger structure/tests, preservation/evidence/full-table/full-prompt/local-link/
diff checks passed; prior protected source/papers/audits/evidence/manifests and31
rows unchanged, exactly EC-T0032 appended. No unrelated diagnostics/trivial tests.

[Evidence](../theorems/frozen/VERIFICATION-S057/README.md). Own source published
before clean clone. Commit/push branch, merge/push main and compare remote SHAs;
final identities retained in Git/observed publication checks. Continue S058 under
standing owner authorisation until told to stop.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep and normalization/key/count and raw threshold prerequisites frozen | Concrete rule integration and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S057 froze the raw threshold exclusion certificate as EC-T0032 after a new exact-source Gate Z check; 32 bundles are frozen and material-class coverage is unchanged.

## Full installed S058 prompt

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
