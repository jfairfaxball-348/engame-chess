# S040 — Conditional raw prefix and prospective-ply clock certificate

2026-10-20; base main 6b2d12a94bb72d4c22487aa6352501d6a0545cb7,
branch session/s040-clock-budget. Explicit all-heads fetch found no earlier
unmerged session. Existing checkout, publication authorised. Owner requested
consecutive sessions until stopped; S041 follows this completed session.

## Result and proof fidelity

**EC-C026 FORMAL_VERIFIED, Gate Z pending.** One new main in
RawClock/BudgetCertificate.lean, imports frozen EC-T0023 unchanged:

Under clock(s.trace)+n<100, EVERY k≤n and actual Extends k s u satisfies
clock(u.trace)<100 AND (k<n → EVERY RawBoardStep u v has clock(v.trace)<100).

The root budget is an explicit hypothesis; no numerical mate bound is supplied.
Full initial-rooted histories, actual Moves/legal witnesses and all raw replies
are retained. The prospective child is universally quantified, even outside a
strategy and for adverse/reset/draw-ending moves. It need not be played as a
claim action. k=n bounds only the current prefix; n=0 gives no prospective ply.
Proof applies frozen growth at k, and at k+1 via actual Extends.snoc, using
k+1≤n, monotone addition and transitivity. All units BOARD PLIES. No erased-board
surrogate, arbitrary seeded counter, endpoint-clock premise or terminal filter.
One theorem module, no extra definitions/redundant elementary declarations.

[Paper](../proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md) and
[paper audit](../audits/EC-C026_RAW_CLOCK_BUDGET_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C026_RAW_CLOCK_BUDGET_LEAN.md). Same-agent review,
not independent external audit. Symbolic controls cover n=0, k=0, k=n, strict
99/100 boundary, quiet/reset/mixed paths, equal erasures with distinct histories,
and earlier raw draws. No concrete compatible full game was run/asserted.
Classical arithmetic, no novelty, tablebase, engine, enumeration or certificates.

## Observed checks and exact source

Published own exact source **dd24ef3b4bd68d429c9c381908a7f3d5bfa9f85f** BEFORE one NEW GitHub clone
**/tmp/engame-s040-gate-f**, detached FULL SHA, no formal/.lake before build.
Full **69-job lake build, exit 0, 442.648s**; COMPLETE **AxiomCheck exit 0**,
UTC **2026-10-20T08:07:13Z**, **273 allowed reports** (241 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free). Main standard-three only.
Exact statement inspected. Working/clean runner outputs identical; every
formal source matches exact anchor. Source/transitive hashes and clean-source
HEAD/tree/status retained. New module forbidden-token scan zero.

Incremental build/complete authoring runner passed FIRST ATTEMPT. The initial
fresh verifier invocation mistakenly used short SHA dd24ef3: clone/checkout
passed, strict full-HEAD comparison stopped BEFORE any Lean command. The same
new clone was observed at correct full SHA without .lake; retained prebuild
resume mode checked this, performed exact FULL-SHA checkout and ONE build/runner.
Original command records, short checkout and failure note retained. No Lean
build repeated; no formal statement weakened. Reproducer default still requires
a fresh clone; only infrastructure gained an explicit guarded resume option.

Official unmodified core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no new dependency/shim. Existing elan/Git proxy sufficient, TLS/checksums unchanged.
Runtime current, connected, unrestricted/enforced, no new secret/configuration.
Hosted CI unobserved. [Full evidence](evidence/S040/README.md).
Relevant source/record preservation, ledger structure, evidence/table/full-prompt/
local-link/diff checks passed. No unrelated diagnostics or trivial tests.

## Preservation and limits

Twenty-three frozen bundles unchanged; no frozen source, prior candidate source,
paper, audit, session/evidence, manifest or ledger row edited. Aggregate Lean
files additive only. EC-C026 added and status grounded in observed Gate F.
The certificate proves no FIDE CanClaim predicate false, repetition certificate/
key correctness, no-earlier-terminal admissibility, current/intended claim
semantics, automatic fivefold/75-move adjudication, mate precedence, full Layer
A/B/C instance, strategy extraction, rule-aware lifting, numerical KRK bound,
holding/outcome, DTM/DTZ/WDL/Syzygy parity or initial-position value.
S041 installs separate exact-source Gate Z for this one module; full preceding
history and all defender claims remain separate. Session commits/pushes branch,
merges/pushes main and checks matching remote SHAs; final identity in Git history
and observed publication checks. Continuous execution proceeds to installed S041.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing, generic projection, raw traces, counter and multi-step clock bound frozen; conditional clock certificate formally verified | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S040 formally verified the conditional raw prefix and prospective-ply clock certificate; 23 bundles remain frozen and material-class coverage is unchanged.

## Full installed S041 prompt

# NEXT SESSION — S041: Freeze the conditional raw clock certificate

Execute as the next authorised session. Follow AGENTS.md: fetch ALL remote
heads explicitly, merge earlier unmerged session work, read latest main's prompt,
use existing checkout, no worktree. Publication authorised. End committed/pushed
on the session branch, merged/pushed to main, compare remote SHAs, never force
main. Update and reproduce the FULL stable progress table in closeout and owner
report, Syzygy parity LAST, then one sentence session delta. No class-count
upgrade from theorem bundle counts. Consecutive execution remains authorised
until the owner says stop.

## Starting point and reading

S040 establishes EC-C026 at Gate F only. Its OWN exact published proof-source:
`dd24ef3b4bd68d429c9c381908a7f3d5bfa9f85f`.
Read docs/CHARTER.md, docs/PROOF_PROTOCOL.md, docs/ROADMAP.md,
research/CANDIDATES.md and research/KRK_RULE_DISTANCE_SPEC.md §§4–5. Read
EC-T0021/0022/0023 manifests and definitions, actual S039 freeze evidence,
proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md, both EC-C026 audits,
sessions/S040_RAW_CLOCK_BUDGET_CERTIFICATE.md and actual sessions/evidence/S040/
logs, summary, full source/transitive hashes and clean-source identities.
Twenty-three frozen bundles; full FIDE history/claims and numerical KRK open.

## Principal task: one exact-source Gate Z review and freeze

Review paper/Lean fidelity BEFORE freeze. The one new complete module is
formal/EndgameChess/Rules/RawClock/BudgetCertificate.lean. Its sole main is
EndgameChess.Rules.RawClock.clock_budget_certificate:

For every s,n, under clock(s.trace)+n<100, for every k≤n and Extends k s u,
clock(u.trace)<100 AND
(k<n → ∀ v, RawBoardStep u v → clock(v.trace)<100).

The hypothesis is explicit, not a uniform KRK result. The prospective child
ranges over EVERY raw legal append, even outside a strategy and draw-ending
children; it is not an executed claim action. At k=n only the current prefix
is bounded; n=0 grants no prospective ply. All indices are BOARD PLIES.
The proof applies frozen growth to the given path and actual Extends.snoc,
uses k+1≤n and monotone addition/transitivity. Full traces, legality witnesses,
resets and equal-erasure history distinctions are retained. No endpoint-clock
premise, ReachK surrogate, arbitrary seeds, terminal or material/colour filter.

Use ONE NEW GitHub Gate Z clone at the OWN FULL exact SHA above; no formal/.lake
before build. Run full lake build THEN COMPLETE AxiomCheck. Inspect the exact
new main statement/report: only propext/Classical.choice/Quot.sound subset.
Retain full logs, exits/timings, UTC, official toolchain identity, full source/
transitive hashes and clean-source identities. Compare the whole report with
actual S040 Gate F output; no cached build or previous clone reuse. Source is
already published: do not re-anchor unchanged code. The S040 prebuild verifier
initially rejected a short SHA before any Lean command; its same fresh clone
then checked the FULL SHA and ran ONE build/runner. Retain that prior evidence;
this Gate Z is a separate NEW clone/run.

Only on actual success freeze EC-C026 as next unused ID, expected EC-T0024
(inspect ledger first). Add one immutable manifest recording full module,
exact theorem/axioms, paper/audit/trust links, this own source SHA and fresh
Gate Z evidence. Append exactly one ledger row preserving all prior rows.
If blocked/fidelity fails, record the blocker and do not freeze or edit prior
source. No Lean change or incremental build is expected for this session.

## Audit controls and limits

Recheck n=0, k=0, k=n, strict sums 99/100, quiet/reset/mixed paths, every
prospective reply, equal boards with different histories and earlier raw draws.
Controls symbolic only; no fixed initial-rooted promotion/ep/castling/threshold
game was run or is required. Never prune adverse draw-ending children.
This is a conditional CLOCK certificate, not a theorem that FIDE CanClaim is
false, repetition control/key correctness, no-earlier-terminal admissibility,
claim semantics, automatic fivefold/75-move adjudication, mate precedence,
full Layer instance, strategy extraction, rule-aware lifting, numerical KRK
mate bound, holding/outcome, DTM/DTZ/WDL/Syzygy or initial-position value.
No tablebase, engine, enumeration, stored-position certificate or novelty claim.

## Verification, next obligation and closeout

Preserve all prior formal/candidate/frozen source, papers/audits/evidence and
manifests; prior ledger bytes are a prefix with only one new row appended.
Aggregate imports/runner remain unchanged unless actually needed additively.
Run ledger structure/tests and relevant preservation/evidence/document checks;
no unrelated diagnostic suite or new trivial tests.

Update candidate status, roadmap/README/theorem index, session ledger and
progress table; write sessions/S041_FREEZE_RAW_CLOCK_BUDGET.md with complete
observed evidence and FULL installed S042 prompt. Select the next narrow
obligation from actual results. One useful next prerequisite is full-history
occurrence counting for an explicit arbitrary Position→Key map with decidable
key equality, retaining the root and proving an exact append count law from
frozen append_spec. If selected, its generic key MUST NOT be claimed to be the
FIDE repetition key: effective legal en-passant, rights/history fidelity and
claim/adjudication semantics remain separate. Avoid assuming a repetition
certificate or a numerical mate bound. Fix a well-posed statement before Lean.
Commit/push session branch, merge/push main and compare remote SHAs. Hosted CI
remains unobserved unless actually inspected. Continue only the installed prompt.

## Cloud activation

Use runtime skill and inspect network policy; reuse inherited Git proxy.
Official core Lean4.35.0, no new dependency. ELAN_HOME=/workspace/.tools/elan;
prepend bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time,
TLS/checksums unchanged. Existing environment suffices absent an actual blocker.
