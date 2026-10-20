# S060 — Raw mate-first endpoint classifier ongoing guards

2026-10-20, base main 7fa1f04e19c9f6ceaab505cb2e80311c60d20ea3,
branch session/s060-raw-endpoint-classifier. All-heads fetch, no prior unmerged
work, existing checkout; consecutive sessions/publication authorised.
EC-C036 FORMAL_VERIFIED, Gate Z pending.

Selected next concrete prerequisite after reviewing S032 §4 and existing kernel.
NEW RawAdjudication Stalemated/DrawTrigger/EndpointStatus/classify definitions:
MatedK first gives opposite-turn winner, then stalemate/dead/150-ply/fivefold gives
draw, otherwise ongoing. Main exact ongoing IFF nondead, some actual kernel Legal
successor, clock<150/count<5. Forward no-successor Bool check split yields mate or
stalemate contradiction; reverse successor refutes mate/stale then all draw
triggers excluded. No legal reply pruned. All raw states/traces/flags/colours;
no valid-history/material assumption. Optional100/3 claims remain separate.

[Paper](../proofs/EC-C036_RAW_ENDPOINT_CLASSIFIER.md),
[paper audit](../audits/EC-C036_ENDPOINT_PAPER.md),
[Lean fidelity](../audits/EC-C036_ENDPOINT_LEAN.md).

Raw classifier component, NOT full FIDE adjudication/history correctness. Mate
priority at150 explicit; mate/fivefold malformed overlap priority is chosen raw
model, not extra Article9.6.1 precedence. Admissibility excludes feasible overlap
only after a separate proof. Existing S032 rules mapping retained, not redone.
No full key/rights-history, no-earlier-terminal histories/real claim protocol,
concrete FIDE Layer/strategy lifting, numerical KRK, holding/outcome, WDL/DTZ or
initial value. Paper and separate audit BEFORE Lean; same-agent review, not
independent external audit.149/150,4/5,optional100/3,mate/stale/dead overlap,
no-successor controls symbolic, no full-game diagnostic/enumeration/oracle/stored
certificate/novelty. Existing retained FIDE source used, no new retrieval.

## Observed verification and publication

Own source `c3cbef551dbf7e16d002815d0a508540439e6ef6`; NEW GitHub clone `/tmp/engame-s060-gate-f`, no .lake before build. Full 86-job build exit 0, 479.369s; COMPLETE AxiomCheck exit 0 at 2026-10-20T13:53:49Z, 283 allowed reports. Main standard-three; whole working/clean report identical.

Exact main inspected, every formal byte matches own anchor; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Both new modules forbidden scan zero.
Incremental 86-job build/full working runner and clean verification passed FIRST
attempt, no warnings/failures/repeated clean build. Relevant ledger/evidence/
preservation/full-table/full-prompt/local-link/diff checks passed; all prior
protected files/33 rows unchanged, aggregate imports/runner additive. No unrelated
diagnostics/trivial tests. Hosted CI unobserved; existing environment/proxy sufficient.

[Evidence](evidence/S060/README.md). Own source pushed before clean clone;
closeout commit/push branch, merge/push main and remote identity verified and
retained in Git/observed publication. Continue installed S061 until stopped.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep and normalization/key/count and raw threshold/exact exclusion prerequisites frozen; raw ongoing classifier formally verified | Concrete rule integration and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S060 formally verified exact ongoing guards for the raw mate-first endpoint classifier; 33 bundles remain frozen and material-class coverage is unchanged.

## Full installed S061 prompt

# NEXT SESSION — S061: Freeze raw mate-first ongoing characterization

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Fetch ALL remote heads, merge prior unmerged work, latest main,
existing checkout. Commit/push branch, merge/push main, compare remote identities;
never force main. FULL stable progress table, Syzygy last, immediate session delta.

S060 formally verified EC-C036 at OWN full proof-source
c3cbef551dbf7e16d002815d0a508540439e6ef6; 33 bundles frozen before this session.
Read actual evidence/closeout, paper/audits, complete RawAdjudication Definitions/
Ongoing, frozen kernel MatedK/DeadK, RawTrace/count/clock dependencies, S032 §4,
charter/protocol/roadmap/candidates. Existing source record covers FIDE2023 Articles5/9.

Separate exact-source Gate Z, no Lean edits. Main ongoing_iff: mate-first raw
classify s=ongoing iff nondead, some actual Legal successor, clock<150/count<5.
Review no-successor check Bool split (mate vs stalemate), converse successor
refutes mate/stale, nondead/strict thresholds refute all DrawTrigger disjuncts.
Mate first at150; malformed mate/fivefold raw overlap priority is model definition,
NOT extra FIDE9.6.1 precedence claim.100/3 optional claims remain separate actions.
All actual raw states/flags/colours/traces, no history/material/terminal pruning.
Same-agent audit, not independent external audit; no oracle/enumeration/certificates/
concrete full-game diagnostic/novelty claim. Classifier not certified full FIDE
adjudication; key/rights-history and no-earlier-terminal admissibility still open.

ONE NEW GitHub clone at OWN FULL SHA above, no .lake before full build then
COMPLETE AxiomCheck; exact main/standard-three subsets. Whole S060 report/formal
bytes equality, full source/transitive SHA256, clean HEAD/tree/status, complete
logs/commands/exits/times/UTC/toolchain/executable. Official core Lean4.35.0,
no dependencies/shim, one fresh build at a time; interruptions/retries retained.
Hosted CI unobserved unless inspected. Only observed success permits EC-T0034/v1.md
freezing BOTH complete RawAdjudication Definitions/Ongoing and one appended ledger
row. Prior protected files/33 rows unchanged; no incremental build absent source
edit. Relevant ledger tests/structure/evidence/preservation/full-table/full-prompt/
local-link/diff checks; no unrelated diagnostics/trivial tests.

Update candidate/roadmap/README/session ledger/theorems index/progress; write
sessions/S061_FREEZE_RAW_ENDPOINT_CLASSIFIER.md with actual evidence and FULL
installed S062 prompt. Commit/push/merge/push and compare remotes; continue until stopped.

For S062 select stopped-history legal-reply lifting after complete paper/audit:
NEW Admissible predicate on frozen initial-rooted indexed Trace, recursively true
at start and at snoc iff prior trace admissible AND prior endpoint raw classify
ongoing. Current endpoint MAY be terminal; only strict prefixes ongoing. Trace
records board moves only, no successful claim. This is relative to chosen raw
classifier, NOT yet certified full FIDE history correspondence. Keep actual
source trace/move/hm, no erased-history replacement.

A useful ONE main theorem may combine exact append admissibility equivalence
(admissible child iff admissible parent AND parent ongoing) with lift of EVERY
kernel Legal successor from an admissible ongoing source to the actual stored
append, including children that immediately draw/mate. Do not require child ongoing
or remove adverse terminal-ending replies. Use frozen raw append/lifting and
classifier guards; no new game model that prunes draws. Consider definitions
separate and one main module; complete exact local argument before EC-C037/Lean.

No full FIDE key/rights-history identity, terminal/claim protocol correctness,
full concrete FIDE Layer, strategy lifting, numerical KRK, holding/outcome,
WDL/DTZ/Syzygy or initial-position result follows from this raw classifier.
Use available runtime guidance/status/network policy, inherited proxy/CA,
ELAN_HOME=/workspace/.tools/elan. Lake in formal/, Python root; official core
Lean4.35.0, TLS/checksums unchanged.
