# S042 — Generic full raw-history key occurrences

2026-10-20, base main 62052f4d87c0fac3e224cb964408dd315ea60fea;
branch session/s042-raw-key-occurrences. Explicit all-heads fetch, no earlier
unmerged sessions, existing checkout. Publication/consecutive sessions authorised.

## Result and scope

**EC-C027 FORMAL_VERIFIED, Gate Z pending.** Shared RawOccurrences/Definitions
and one main in RawOccurrences/Append; aggregate imports/runner additive only.
Fixed arbitrary key:Position→K with explicit DecidableEq K. Count is length of
all t.positions entries satisfying decide(key(p)=a), retaining initial/root,
current and every earlier endpoint. Every legal actual append obeys exactly
occ(child,a)=occ(parent,a)+(if key(new endpoint)=a then 1 else 0).
Proof uses frozen append_spec position-list equality, filter append and singleton
length. Same key/query on both sides; new-current count queries NEW key in OLD
history, not prior-current count+1. No clock reset truncation, independent vector,
arbitrary Boolean equality, erased-history surrogate or terminal/material/side/
strategy filter. All reset/adverse draw-ending legal children remain covered.

[Paper](../proofs/EC-C027_RAW_KEY_OCCURRENCES.md) and
[paper audit](../audits/EC-C027_RAW_KEY_OCCURRENCES_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C027_RAW_KEY_OCCURRENCES_LEAN.md). Same-agent reviews,
not independent external audit. Symbolic root/absent/equal/new/nonconsecutive/
constant-key/equal-erasure/reset/earlier-draw controls; [A,B,A] followed by B
illustrates why old-current count+1 is wrong. No such list claimed as a full
compatible chess game; no promotion/ep/castling/threshold prefix constructed/run.
Classical list counting, no novelty, engine/tablebase/enumeration/certificates.

## Observed verification

Own source **04bd8d03bf09056eff74c5fae1c399a841b170cb** published BEFORE ONE NEW GitHub clone
**/tmp/engame-s042-gate-f**, detached FULL exact SHA, formal/.lake absent before build.
Full **71-job lake build exit 0, 446.759s**; COMPLETE **AxiomCheck exit 0**,
UTC **2026-10-20T08:26:11Z**, **274 allowed reports** (242 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free). Main standard-three only.
Definition/main exact output inspected. Full working/clean reports identical;
all source/transitive bytes match exact anchor, clean HEAD/tree/status retained.
Two new modules forbidden scan zero. Original incremental build/complete runner
passed FIRST attempt; no failed command/prebuild or repeated clean build.

Official unmodified core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim. Existing elan/Git proxy/network policy sufficient, no setup
change, TLS/checksums unchanged. Hosted CI unobserved. [Evidence](evidence/S042/README.md).
Relevant source/record preservation, ledger structure, evidence/table/full-prompt/
local-link/diff checks passed; no unrelated diagnostics or trivial tests.
Twenty-four frozen bundles unchanged, no ledger row/manifest added or prior
formal/candidate source, paper/audit/session/evidence modified. Aggregates additive.

## Limits and next session

Generic map may be constant, so this is NOT a FIDE repetition-key theorem.
No effective-legal-ep/Article 9.2.3/rights-history correctness, low-repetition
certificate, current/intended claim classifier, lawful-terminal admissibility,
automatic fivefold/75-move adjudication/mate precedence, full Layer/strategy
extraction/lifting, numerical KRK mate bound, holding/outcome, DTM/DTZ/WDL/
Syzygy parity or initial-position value. No all-KRK low-count/clock budget claim.
S043 installs separate exact-source freeze of this bundle. A later narrowly
specified legal-ep availability/effective-target prerequisite may precede any
actual repetition-key choice; kernel play's epCapture is local, not exported.
Commit/push branch, merge/push main and compare remote SHAs; final identity is
in Git history and observed publication checks. Continue installed S043.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing, generic projection, raw traces, counter, multi-step bound and conditional clock certificate frozen; generic key-count append law formally verified | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S042 formally verified generic full-history key occurrence counting and its exact append law; 24 bundles remain frozen and material-class coverage is unchanged.

## Full installed S043 prompt

# NEXT SESSION — S043: Freeze generic full-history key occurrence counting

Execute as next authorised session. Follow AGENTS.md: explicitly fetch ALL remote
heads, merge earlier unmerged work, read latest main prompt, existing checkout,
no worktree. Publication authorised. Commit/push branch, merge/push main, compare
remote SHAs; never force main. Update/reproduce FULL stable progress table in
closeout/owner report, Syzygy parity LAST, one sentence delta below. Continue
installed sessions until owner stops. Bundles are not solved material classes.

## Starting point and reading

S042 established EC-C027 at Gate F only, OWN full published proof-source:
`04bd8d03bf09056eff74c5fae1c399a841b170cb`.
Read charter/protocol/roadmap/candidates, research/KRK_RULE_DISTANCE_SPEC.md
(repetition/claims), EC-T0021–0024 manifests, frozen RawTrace definitions and
append_spec, proofs/EC-C027_RAW_KEY_OCCURRENCES.md and both EC-C027 audits,
sessions/S042_RAW_KEY_OCCURRENCES.md and actual sessions/evidence/S042/ full
logs, summary, source/transitive hashes and clean-source identity. Twenty-four
bundles frozen; generic counting is not a FIDE repetition instance.

## Principal task: one OWN exact-source Gate Z obligation

Review paper-to-Lean fidelity before freeze. Complete new bundle boundary:
- formal/EndgameChess/Rules/RawOccurrences/Definitions.lean
- formal/EndgameChess/Rules/RawOccurrences/Append.lean

One main: EndgameChess.Rules.RawOccurrences.append_occurrences.
For arbitrary K:Type u with explicit DecidableEq K and FIXED key:Position→K,
occurrences counts ALL positions in frozen t.positions, including root/current,
using correct equality decision. For EVERY raw s, actual legal m and queried a:

 occ(key,append(s,m,hm).trace,a)
   = occ(key,s.trace,a)+(if key(play(erase s)m)=a then 1 else 0).

Proof rewrites frozen append_spec's position-list equality and ordinary
filter/length append laws; equality split handles the singleton. No clock reset
truncation, independent count vector, arbitrary Boolean equality, erased-board
history substitution, terminal/material/colour/strategy filter or fabricated
compatible KRK history. Querying the child's current key means querying that
NEW key in the OLD history, not incrementing the prior current-key count.

Use ONE NEW GitHub Gate Z clone at OWN full exact SHA above, no formal/.lake
before build. Full lake build THEN COMPLETE AxiomCheck must pass. Inspect exact
printed definition/main statement and only propext/Classical.choice/Quot.sound
subset axioms. Retain full logs, commands/exits/timings, UTC, official Lean
identity, all source/transitive hashes, clean HEAD/tree/status. Compare entire
report with actual S042 Gate F. No reuse of old clone/cache, no re-anchor of
unchanged source. No Lean edits/incremental build expected.

Only upon actual success freeze EC-C027 as next unused ID, expected EC-T0025
(inspect actual ledger). Add immutable manifest with COMPLETE module boundary,
exact definition/statement/source, axioms, own SHA, paper/audit/trust links and
new Gate Z evidence. Append exactly one ledger row preserving prior bytes.
If fidelity/build fails, record blocker; do not freeze, edit frozen source or
manufacture success. All earlier papers/audits/evidence stay immutable.

## Audit and semantic limits

Recheck empty-move root (one position), absent/equal/new keys, nonconsecutive
repeats, constant key, equal erasures with different histories, resets and an
earlier raw draw. Symbolic key-list [A,B,A] followed by B makes the new-current
B count 2, while prior-current A count+1 would wrongly yield 3. Do not claim
such a list is a compatible full chess game. No fixed initial-rooted promotion/
ep/castling/threshold prefix is required or asserted.
Generic key may be constant; it is NOT automatically a FIDE repetition key.
No effective legal en-passant, Article 9.2.3/rights-history correctness, repetition
threshold certificate, current/intended claims, admissibility/adjudication/mate
precedence, full Layer/strategy extraction/lifting, numerical KRK bounds,
holding/outcome, WDL/DTZ/Syzygy or initial-position result follows. No claim
that all KRK histories have low repetition or clock+n<100. No adverse legal
reply pruned. Classical list counting, no novelty/tablebase/engine/enumeration.

## Verification, next obligation and closeout

Preserve all prior formal/candidate/frozen source, papers/audits/evidence and
manifests. Prior ledger bytes are a prefix plus exactly one new row. Aggregate
Lean files unchanged unless actually needed additively. Run relevant ledger
structure/tests, preservation/evidence/document checks; no unrelated diagnostic
suite or trivial tests. Update candidates, roadmap/README/theorem index,
session ledger and progress table. Write sessions/S043_FREEZE_RAW_KEY_OCCURRENCES.md
with complete observed evidence and FULL installed S044 prompt.

Choose the next small obligation from actual results. A useful next prerequisite
is legality-filtered en-passant availability/effective target before selecting
a repetition key. Inspect actual frozen Moves.play: its epCapture test is a
LOCAL let, not an exported predicate. Define the source pawn/flag/diagonal/
empty-destination capture event explicitly, require isLegal=true, and state
precisely what an effective ep target means. Existence of a pseudo-legal ep
move is insufficient (pins). Avoid claiming full FIDE key correspondence or
fabricating a compatible prefix. Fix an exact paper/audit before Lean and keep
the next session narrow. Effective rights/history/claims remain separate.

Commit/push/merge/push and compare remote SHAs; distinguish hosted CI if
unobserved. Continue only the installed next prompt under standing authorisation.

## Cloud activation

Use available runtime guidance, inspect network policy, reuse inherited Git
proxy. Official core Lean4.35.0, no dependency. ELAN_HOME=/workspace/.tools/elan;
prepend bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time;
TLS/checksums unchanged. Existing environment suffices absent an actual blocker.
