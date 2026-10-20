# S043 — Freeze generic full raw-history key occurrence counting

2026-10-20, base main 28c3cc300f34638387fffc45fb899192923fc642,
branch session/s043-freeze-raw-key-occurrences. Explicit all-heads fetch, no
prior unmerged session, existing checkout, publication/consecutive run authorised.

## Result and checks

**EC-C027 frozen as EC-T0025**, twenty-five bundles, no class coverage upgrade.
No Lean source edits. Paper/source review confirms fixed arbitrary key map and
explicit DecidableEq, full root/prior/current position counting, frozen append
retention and exact new-key singleton contribution. New-current count queries
NEW key in OLD history; no reset truncation, vector/seed, erased-history shortcut
or material/side/strategy/terminal filter. Every raw legal append retained.
Same-agent review, not independent external audit; symbolic empty-root/absent/
equal/new/nonconsecutive/constant-key/equal-erasure/reset/earlier-draw controls
found no gap. [A,B,A]→B illustrates the old-current-count mistake, not a full
compatible game. No promotion/ep/castling/threshold prefix run or required.
Classical list counting, no novelty/tablebase/engine/enumeration/certificates.

OWN source **04bd8d03bf09056eff74c5fae1c399a841b170cb**, ONE NEW GitHub clone
**/tmp/engame-s043-gate-z**, detached FULL exact SHA, no .lake before build.
Full **71-job lake build exit 0, 435.817s**, COMPLETE **AxiomCheck exit 0**,
UTC **2026-10-20T08:34:45Z**, **274 allowed reports**, main standard-three only.
Exact definition/main inspected. Whole output identical to actual S042 Gate F;
all source/transitive hashes, clean HEAD/tree/status and commands/exits/timings
retained. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim, setup change or
TLS/checksum bypass. Existing elan/Git proxy sufficient. Hosted CI unobserved.
[Evidence](../theorems/frozen/VERIFICATION-S043/README.md).

One immutable manifest/new ledger row, all prior formal source/papers/audits/
session/evidence/manifests and 24 rows preserved. Relevant ledger structure/tests,
preservation/evidence and full table/prompt/local-link/diff checks passed.
No incremental build required without source edits, no unrelated diagnostics
or trivial tests. Commit/push session branch, merge/push main and compare remote
SHAs; final identity in Git history and observed publication checks. Continue S044.

## Limits and next prerequisite

Generic key may be constant: no FIDE repetition key/effective-ep/rights-history/
Article 9.2.3 correspondence or low-repetition certificate. No claims/terminal
admissibility/adjudication/mate precedence, full Layer/strategy extraction/lifting,
numerical KRK bound, holding/outcome, DTM/DTZ/WDL/Syzygy or initial-position value.
S044 chooses precise legality-filtered ep event and effective-target spec before
key composition. play's epCapture is local, not exported; isLegal required,
not just pseudo-legality. No full repetition semantics are inferred.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw trace/clock and generic key counting frozen | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S043 froze generic raw key occurrence counting as EC-T0025 after a new exact-source Gate Z check; 25 bundles are frozen and material-class coverage is unchanged.

## Full installed S044 prompt

# NEXT SESSION — S044: Legality-filtered en-passant availability and effective target

Execute as next authorised session. Follow AGENTS.md: explicitly fetch ALL remote
heads, merge earlier unmerged sessions, read latest main prompt, existing checkout,
no worktree. Publication authorised. Commit/push branch, merge/push main, compare
remote SHAs; never force main. Update/reproduce FULL stable progress table in
closeout and owner report, Syzygy parity LAST, one-sentence delta below. Continue
installed sessions until owner stops. Bundles are not solved material classes.

## Starting point and reading

S043 froze EC-C027 as EC-T0025 at own source
`04bd8d03bf09056eff74c5fae1c399a841b170cb` after NEW exact-source Gate Z.
Read actual EC-T0025 manifest/VERIFICATION-S043 evidence, generic occurrence
paper/audits, EC-T0021–0024 manifests and actual RawTrace/RawClock definitions,
research/KRK_RULE_DISTANCE_SPEC.md §§2–5, frozen Moves.pawnMoveOK/isLegal/play,
charter/protocol/roadmap/candidates and S042/S043 closeouts. Twenty-five bundles
frozen, full FIDE repetition/key/adjudication and numerical KRK remain open.

## Principal task: one narrow effective-ep specification

Write standalone exact paper and adversarial audit BEFORE Lean; then register
EC-C028 only after the statement is well posed. Add NEW modules only: shared
definitions separate, one combined main specification theorem in its own module.
Keep every frozen source unchanged; add aggregate imports/runner additively.

At raw kernel Position q and actual Move m define LegalEP(q,m) explicitly by:
- isLegal q m = true;
- q.board m.src = some (q.turn,pawn), before any promotion;
- q.ep = some m.dst;
- m.src.file ≠ m.dst.file;
- q.board m.dst = none;
- q.board (m.dst.file,m.src.rank) = some (q.turn.opp,pawn).

This is the legal en-passant event matching the existing RawClock CaptureEvent
EP branch and kernel play's source/flag/diagonal/empty-destination removal test.
Do not pretend epCapture is exported: it is a LOCAL let inside play. Require
actual isLegal, not merely isPseudo/pawnMoveOK: pinned/self-check cases must not
activate an effective target. Reuse frozen Pawn definition if useful. No global
material-count equivalence or full FIDE Article 9.2.3 theorem is asserted.

Define effectiveEP(q) as q.ep if some m satisfies LegalEP(q,m), and none otherwise.
An explicitly noncomputable classical existence decision is acceptable; do not
add enumeration, dependencies, stored certificates, fabricated game prefixes or
an executable-search claim. Fix the exact construction in the paper first.

Prove one combined main specification, for EVERY raw q:

 (effectiveEP(q)=none ↔ ¬∃m, LegalEP(q,m)) AND
 (∀ dst, effectiveEP(q)=some dst ↔ ∃m, LegalEP(q,m) ∧ m.dst=dst).

The event's q.ep=some m.dst implies no witness when q.ep=none and forces all
witnesses to the same target. Thus returning q.ep when a witness exists cannot
return none or a different target. This target-consistency argument is required,
not an unproved assumption. Quantification covers both colours/flags/material;
no terminal/strategy filter or independent history/count/clock seed.

## Audit and limits

Audit absent raw ep flag, ep flag without any eligible pawn, only pseudo-legal
but no legal ep due to self-check, multiple legal sources for one target,
occupied destination, wrong source kind/colour, wrong flank pawn, and ordinary
pawn/capture moves. Use symbolic implications of the exact predicate; do not
claim actual initial-rooted promotion/ep/castling/threshold games were run.
Pin-sensitive eligibility follows from requiring isLegal; do not fabricate a
specific pinned-board witness unless actually constructed/checked. No extra
trivial theorem modules for every clause are needed.

This is ONLY legality-filtered effective-target bookkeeping. It does not choose
or certify a full repetition key, prove Article 9.2.3/rights-history equivalence,
low-repetition certificate, claim classifier, no-earlier-terminal admissibility,
automatic draw/mate precedence, full Layer/strategy extraction/lifting, numerical
KRK bound, holding/outcome, WDL/DTZ/Syzygy or initial-position value. Generic key
counting is already frozen, but no new FIDE claim conclusion follows from it.
No tablebase, engine, enumeration, arbitrary-clock KRK witness or novelty claim.

## Verification and closeout

Run changed modules/importers incrementally. Publish proof-source BEFORE ONE NEW
GitHub Gate F clone at FULL exact SHA, no formal/.lake before build. Full lake
build THEN COMPLETE AxiomCheck must actually pass. Inspect exact definition/main
statement and allowed propext/Classical.choice/Quot.sound subsets. Retain full
logs/exits/timings/UTC, official toolchain, source/transitive hashes and clean
HEAD/tree/status; compare full working/clean outputs. Gate Z separate: no new
frozen row/manifest. Preserve all prior source/papers/audits/evidence/ledger bytes;
aggregate Lean files only gain additive entries. No unrelated diagnostics/tests.

Update candidates, roadmap/README, session ledger and progress table. Write
sessions/S044_EFFECTIVE_EP_TARGET.md with actual evidence and FULL installed S045
prompt. Consider separate exact-source freeze before further key composition.
Run relevant ledger/evidence/preservation/document checks, commit/push/merge/push
and verify remote SHAs. Hosted CI unobserved unless actually inspected. Continue
only the installed next prompt under standing authorisation.

## Cloud activation

Use available runtime guidance, inspect network policy, reuse inherited Git proxy.
Official core Lean4.35.0, no dependency. ELAN_HOME=/workspace/.tools/elan; prepend
bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time, TLS/
checksums unchanged. Existing environment suffices absent actual blocker.
