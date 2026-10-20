# S061 — Freeze raw mate-first endpoint classifier

2026-10-20, base main 0314ce63b1684ffde6d92e4237f2f79c460880bc;
branch session/s061-freeze-raw-endpoint-classifier. All-heads fetch, no prior
unmerged work, existing checkout; consecutive sessions/publication authorised.
EC-C036 frozen as EC-T0034, 34 bundles; material-class coverage unchanged.

Raw mate-first classify returns opposite-turn winner at MatedK, draw at remaining
stalemate/dead/150-ply/fivefold triggers, otherwise ongoing. EXACT ongoing iff
nondead, some actual Legal successor, clock<150/count<5. No-successor check Bool
split gives mate/stale forward; converse successor refutes both, remaining draw
triggers false. Optional100/3 claims separate. All raw states/traces/flags/colours,
no legal reply pruning/history/material filter. Raw malformed mate/fivefold overlap
priority is definition, NOT extra FIDE9.6.1 priority; lawful-history proof outstanding.

[Review](../theorems/frozen/VERIFICATION-S061/fidelity-review.md).

Raw component NOT certified full FIDE adjudication. No key/rights-history identity,
no-earlier-terminal histories/real claim protocol, full FIDE Layer/strategy lifting,
numerical KRK, holding/outcome, WDL/DTZ or initial value. Same-agent audit, not
independent external review; symbolic149/150,4/5,optional100/3,overlap/no-successor
controls, no actual full-game diagnostic/enumeration/oracle/certificates/novelty.
Existing S032 rules mapping retained, no new source retrieval.

## Observed verification and publication

Own source `c3cbef551dbf7e16d002815d0a508540439e6ef6`; NEW GitHub clone `/tmp/engame-s061-gate-z`, no .lake before build. Full 86-job build exit 0, 492.419s; COMPLETE AxiomCheck exit 0 at 2026-10-20T14:02:36Z, 283 allowed reports. Main standard-three; full report identical to S060 Gate F.

Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change. One new clean run, no failure/repeated build.
No source edit/incremental build. Relevant ledger tests/structure, preservation/
evidence/full-table/full-prompt/local-link/diff checks passed; prior protected files
and33 rows unchanged, exactly EC-T0034 appended. No unrelated diagnostics/trivial
tests; hosted CI unobserved.

[Evidence](../theorems/frozen/VERIFICATION-S061/README.md). Own source published
before clone. Commit/push branch, merge/push main and compare remote identities,
retained in Git/observed publication; continue installed S062 until owner stops.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep and normalization/key/count and raw threshold/exclusion and endpoint classifier prerequisites frozen | Concrete rule integration and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S061 froze the raw mate-first ongoing characterization as EC-T0034 after a new exact-source Gate Z check; 34 bundles are frozen and material-class coverage is unchanged.

## Full installed S062 prompt

# NEXT SESSION — S062: Stopped-history actual append and full legal-reply lifting

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Fetch ALL remote heads, merge prior unmerged work, latest main,
existing checkout. Commit/push branch, merge/push main, compare remote identities;
never force main. FULL stable progress table, Syzygy last, immediate session delta.

S061 froze EC-C036 as EC-T0034, OWN source
c3cbef551dbf7e16d002815d0a508540439e6ef6; 34 frozen bundles, not solved classes.
Read actual manifest/evidence, S060/61 closeouts, EC-C036 paper/audits, raw endpoint
Definitions/Ongoing, RawTrace indexed definitions/append/completeness/soundness,
HistoryLayer full interface, S032 §2/4, charter/protocol/roadmap/candidates.

## Principal task

Full standalone paper and separate adversarial audit BEFORE Lean, then EC-C037
LOCAL_VERIFIED only after complete exact argument. NEW shared stopped-history
definition over frozen initial-rooted indexed Trace:
Admissible .start := True;
Admissible (@Trace.snoc q prior m hm) := Admissible prior ∧
  RawAdjudication.classify (state with exact endpoint q and exact prior trace)=ongoing.
Inspect actual State constructor/erase names. Use actual stored trace/m/hm, not
an erased-history replacement or arbitrary-seed count vector. This admits terminal
CURRENT endpoint but requires every STRICT prefix ongoing; no successful claim
is present in board-move traces. Relative to CHOSEN RAW classifier only, not yet
certified full FIDE legal-history/rights-key/claim-protocol correspondence.

ONE NEW main theorem/module for every raw state s, combining:
(1) ∀m,∀hm actual legal, Admissible(append s m hm).trace ↔
    Admissible s.trace ∧ classify s=ongoing;
(2) Admissible s.trace → classify s=ongoing → ∀r,Legal(erase s)r →
    ∃t,Admissible t.trace ∧ RawBoardStep s t ∧ erase t=r.

Exact conjunction is one append-and-full-reply interface. Unfold stopped-history
snoc for(1), use actual witness m/hm from Legal plus actual append for(2).
No child-ongoing condition! Every legal child may immediately draw/mate, and
remains lifted. Root .start allowed as current endpoint without requiring any
strict prefix. No future trace after terminal parent admitted. Optional claim
opportunities may be declined; do not treat availability as automatic terminal.
No board-move trace records a successful claim/invalid claim/procedural phase.
Audit zero-length, one-ply, terminal parent vs child, every adverse terminal-ending
reply, exact hm/trace dependence, both colours/promotion/raw flags. Current histories
have initial-rooted q/flags by frozen Trace, but no new historical-rights/FIDE key
correspondence theorem inferred. Same-agent audit transparently named, no independent
external review/full-game diagnostic/novelty/enumeration/oracle/certificates.

## Verification and closeout

Frozen sources untouched; definitions separate, one main module, aggregates additive.
Incremental changed modules/importers and COMPLETE working runner. Publish proof
source BEFORE ONE NEW GitHub Gate F clone at FULL exact SHA, .lake absent before
full build then COMPLETE AxiomCheck, exact main/standard-three subsets. Full logs/
commands/exits/times/UTC/toolchain/executable, all source/transitive SHA256,
clean HEAD/tree/status, whole working/clean output/formal-byte equality. Official
core Lean4.35.0, no dependency/shim, one fresh build; interruptions/retries retained.
Gate Z separate, no frozen manifest/row in S062. Preserve prior protected files/34
rows; relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff
checks; no unrelated diagnostics/trivial tests. Hosted CI unobserved unless inspected.
Record any model/proof gap honestly before changing claim.

Update candidate/roadmap/README/session ledger/progress; write
sessions/S062_STOPPED_HISTORY_LIFTING.md with actual evidence and FULL installed
S063 prompt (consider own-source freeze). Commit/push/merge/push, compare remotes;
continue until owner stops. No full FIDE Layer/adjudication/claim correctness,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ or initial value follows.
Use available runtime guidance/status/network policy, inherited proxy/CA,
ELAN_HOME=/workspace/.tools/elan. Lake in formal/, Python root; official core
Lean4.35.0, TLS/checksums unchanged.
