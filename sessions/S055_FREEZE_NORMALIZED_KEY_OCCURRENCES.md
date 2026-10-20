# S055 — Freeze current normalized-key count law

2026-10-20, base main 6d486105667638870e22ffc666897fce5f53025c,
branch session/s055-freeze-normalized-key-occurrences. Explicit all-heads fetch,
no prior unmerged work, existing checkout; owner authorises consecutive sessions
and publication. EC-C033 frozen as EC-T0031; 31 bundles, no class coverage upgrade.

## Exact result and fidelity

For every raw State s, actual Move m and legality proof hm, currentOccurrences
of actual append equals old FULL history count queried at NEW endpoint plusone.
Concrete wrappers use frozen full normalized key and SAME local classical equality.
Root/prior/current retained, no reset truncation or old-current-plus-one shortcut.
Actual indexed trace/hm unchanged. Frozen generic append law and reflexive new-key
indicator=1. Both colours/all flags/promotions/castling/EP/every actual legal reply;
no history/material/terminal/strategy filter or artificial moves without hm.

Both complete modules frozen unchanged; paper/Lean/evidence fidelity reviewed.
[Review](../theorems/frozen/VERIFICATION-S055/fidelity-review.md).

No full FIDE key/Article9.2.3/rights-history identity, repetition threshold/claim,
no-earlier-terminal histories, automatic-draw/mate precedence adjudication,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial value.
Same-agent review, not independent external audit. Symbolic [A,B,A] thenB control,
not a compatible actual chess-game run. No enumeration/oracle/stored certificate,
executable hash/search or novelty claim.

## Observed verification and publication

Own source `9fccb2f46c0edcd358c25885b1f4cdae0f770233`; NEW GitHub clone `/tmp/engame-s055-gate-z`, no .lake before build. Full 81-job build exit 0 in 453.043s; COMPLETE AxiomCheck exit 0 at 2026-10-20T13:08:44Z; 280 allowed reports. Main standard-three; whole report identical to S054 Gate F.

Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status and full logs/commands/exits/times/UTC/toolchain
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Hosted CI unobserved. One new successful
clean run, no failure/repeated build; no source edit/incremental build. Relevant
ledger structure/tests, preservation/evidence/full-table/full-prompt/local-link/
diff checks passed; prior protected source/papers/audits/evidence/manifests and30
rows unchanged, exactly EC-T0031 appended. No unrelated diagnostics/trivial tests.

[Evidence](../theorems/frozen/VERIFICATION-S055/README.md). Own source published
before clean clone. Commit/push branch, merge/push main and compare remote SHAs;
final identities retained in Git/observed publication checks. Continue S056 under
standing owner authorisation until told to stop.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep and normalization/key/count prerequisites frozen | Concrete rule integration and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S055 froze the current normalized-key count append law as EC-T0031 after a new exact-source Gate Z check; 31 bundles are frozen and material-class coverage is unchanged.

## Full installed S056 prompt

# NEXT SESSION — S056: Raw current/intended threshold exclusion certificate

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Fetch ALL remote heads, merge prior unmerged work, latest main,
existing checkout. Commit/push branch, merge/push main, compare remote identities;
never force main. FULL stable progress table, Syzygy last, immediate session delta.

## Starting point and reading

S055 froze EC-C033 as EC-T0031 at OWN source
9fccb2f46c0edcd358c25885b1f4cdae0f770233; 31 frozen bundles, not solved classes.
Read actual manifest/Gate Z evidence, S054/55 closeouts, EC-C033 paper/audits,
OccurrenceDefinitions/CurrentAppend, RawClock StepBound/ExtensionBound, RawTrace
append, HistoryLayer definitions and research/KRK_RULE_DISTANCE_SPEC.md.
Inspect actual filenames; frozen sources/English-FIDE trust boundary unchanged.

## Principal task and exact scope

Before Lean write standalone exact paper and separate adversarial audit; register
EC-C034 only after complete local argument. Add NEW shared RawClaims/Definitions
with raw bookkeeping predicates (names may be clarified in paper):
CurrentThreshold(s) := 100 ≤ RawClock.clock s.trace ∨
                       3 ≤ RawRepetition.currentOccurrences s.
IntendedThreshold(s) := ∃m,∃hm:isLegal(erase s)m=true,
                         CurrentThreshold(append s m hm).
AvailableThreshold(s) := CurrentThreshold s ∨ IntendedThreshold s.
These explicitly quantify ALL actual legal moves, with pawn/capture resets in
actual child counter. They are NOT certified FIDE CanClaim, successful claim
protocols or lawful-terminal-history semantics. Do not edit frozen Layer.CanClaim
or claim complete concrete FIDE instantiation.

ONE NEW main theorem module. For every raw s, under
 clock(s)+1<100,
 currentOccurrences(s)<3,
 ∀m,∀hm:isLegal(erase s)m=true,
       occurrences s.trace (play(erase s)m)<2,
prove ¬AvailableThreshold s.

Use root clock bound arithmetically, frozen actual append clock≤root+1 for
EVERY legal m/hm, and frozen append_currentOccurrences to turn queried old count<2
into child current count<3. Negate both current and intended disjuncts. No child
or defender intended move excluded; pseudo-only moves correctly lack hm. Current
root count hypothesis separate: intended query premise alone doesn't bound it.
No strategy-tree certificate/numerical KRK witness inferred from these explicit
hypotheses. All raw states/flags/colours/promotions, root/prior/current retained.
No threshold truncation/reset shortcut. Audit equality endpoints99/100,2/3,
no-reply vacuity, zeroing resets, new vs old query and current vs intended claims.

Same-agent review transparently named, not independent external audit; classical
bookkeeping, no novelty/enumeration/tablebase/engine/stored certificates or concrete
full-game diagnostics. If paper finds issue, document before changing statement.

## Verification and closeout

Frozen sources untouched; one new main module and separate definitions; aggregates
additive only. Incremental changed modules/importers and COMPLETE working runner.
Publish proof source BEFORE ONE NEW GitHub Gate F clone at FULL exact SHA, .lake
absent before full build then COMPLETE AxiomCheck. Inspect exact main/standard-three
subsets, retain full logs/commands/exits/times/UTC/toolchain/executable, full source/
transitive SHA256 and clean HEAD/tree/status; compare full working/clean report and
source bytes. Official core Lean4.35.0, no dependency/shim. One fresh build at a
time, infrastructure interruptions/retries honestly preserved. Gate Z separate;
no new frozen manifest/row in S056. Preserve all prior protected files and31 rows.
Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff checks;
no unrelated diagnostics/trivial tests. Hosted CI unobserved unless inspected.

Update candidate/roadmap/README/session ledger/progress; write
sessions/S056_RAW_THRESHOLD_CERTIFICATE.md with actual evidence and FULL installed
S057 prompt (consider own-source freeze). Commit/push/merge/push, compare remotes;
continue under standing authorisation until owner stops.

No full FIDE repetition-key/Article9.2.3/rights-history correspondence, no-earlier-
terminal admissibility, real claim/automatic-draw/mate-precedence adjudication,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ or initial-position result.

Use available cloud runtime guidance/status/network policy, inherited proxy/CA,
ELAN_HOME=/workspace/.tools/elan. Lake in formal/, Python root; official core
Lean4.35.0, TLS/checksums unchanged.
