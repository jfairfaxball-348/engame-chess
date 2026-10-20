# S045 — Freeze legality-filtered effective en-passant target

2026-10-20, base main 70f4230beb8bd328b5aa67135fce5a754d5bafb3,
branch session/s045-freeze-effective-ep-target. Explicit all-heads fetch, no
prior unmerged sessions, existing checkout, publication/consecutive run authorised.

## Result and checks

**EC-C028 frozen as EC-T0026**, twenty-six bundles, no class coverage upgrade.
No Lean source edits. Reviewed actual paper/audits, complete definitions/proof,
Gate F statement/axiom/hash/identity evidence and existing kernel event sources.
LegalEP uses actual legality plus source pawn/raw flag/distinct files/empty dst/
opposing flank pawn, not pseudo-legality. Noncomputable effective target uses
classical existence, not search. Main none/no-witness and some/exact-witness
specification proves target consistency using actual flag and some injectivity.
No seed/endpoint hypothesis or material/colour/strategy/terminal filter; arbitrary
raw flags not certified as lawful histories. Same-agent review, not independent
external audit. Symbolic no-flag/no-pawn/pseudo-only/self-check/multiple-source/
occupied/wrong-kind-colour-flank/ordinary controls; no concrete pinned/full
promotion/ep/castling/threshold history run. Classical, no novelty/tablebase/engine.

OWN source **28bdacfa34995ed3d778bfb2dab1654e46999f0c**, ONE NEW GitHub clone
**/tmp/engame-s045-gate-z**, detached FULL exact SHA, no .lake before build.
Full **73-job lake build exit 0, 441.472s**, COMPLETE **AxiomCheck exit 0**,
UTC **2026-10-20T08:53:23Z**, **275 allowed reports**, main standard-three only.
Exact definitions/main inspected; entire output identical to S044 Gate F.
Every source/transitive hash and clean HEAD/tree/status retained with commands/
exits/timings. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim/setup/TLS/checksum
change; existing elan/Git proxy sufficient. Hosted CI unobserved.
[Evidence](../theorems/frozen/VERIFICATION-S045/README.md). Historical S044 local
compile failure/correction preserved; no source change or incremental check here.

One immutable manifest/new row; all prior formal source/papers/audits/session/
evidence/manifests and 25 rows unchanged. Relevant ledger structure/tests,
preservation/evidence/full table/prompt/local-link/diff checks passed. No unrelated
diagnostics/trivial tests. Commit/push branch, merge/push main, compare remote
SHAs; final identity in Git history/observed publication checks. Continue S046.

## Limits and next prerequisite

No full repetition key/Article9.2.3/rights-history correspondence, low-count
certificate, claims/admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK, holding/outcome, DTM/DTZ/WDL/Syzygy
or initial-position result. S046 selects exact kernel characterization of
LegalEP: actual legal source pawn + distinct files + empty dst should force raw
ep flag and opposing flank pawn via pawnMoveOK's remaining branch. Its paper/
audit must precede Lean, preserving actual legality and finite-file arithmetic.
This precedes any normalization/key composition; no such result assumed here.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw trace/clock and generic key counting frozen; effective-ep target frozen | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S045 froze the legality-filtered effective en-passant target as EC-T0026 after a new exact-source Gate Z check; 26 bundles are frozen and material-class coverage is unchanged.

## Full installed S046 prompt

# NEXT SESSION — S046: Kernel characterization of the legal en-passant event

Execute as next authorised session. Follow AGENTS.md: explicitly fetch ALL remote
heads, merge earlier unmerged work, read latest main prompt, existing checkout/no
worktree. Publication authorised. Commit/push branch, merge/push main, compare
remote SHAs; never force main. Update/reproduce FULL stable progress table in
closeout/owner report, Syzygy parity LAST, one sentence delta below. Continue
installed sessions until owner stops. Bundles are not solved material classes.

## Starting point and reading

S045 froze EC-C028 as EC-T0026 at own full proof-source
`28bdacfa34995ed3d778bfb2dab1654e46999f0c` after NEW exact-source Gate Z.
Read actual EC-T0026 manifest/VERIFICATION-S045 evidence, EC-C028 paper/audits,
RawRepetition definitions/target proof, frozen RawClock Pawn/CaptureEvent,
Moves isLegal/isPseudo/pawnMoveOK/play, Rules.Board dx/dy and finite square
coordinates, charter/protocol/roadmap/candidates, S044/S045 closeouts and S032
rule/distance specification. Twenty-six bundles frozen; full FIDE repetition/
adjudication and numerical KRK bounds open.

## Principal task: one exact kernel-fidelity characterization

Write standalone exact paper and adversarial audit BEFORE Lean, then register
EC-C029. Prove for EVERY raw kernel q and actual Move m:

 LegalEP q m ↔ isLegal q m=true ∧ RawClock.Pawn q m ∧
   m.src.file≠m.dst.file ∧ q.board m.dst=none.

The source pawn is of q.turn. Keep actual isLegal (including promotion fields,
pseudo-legality and self-check); do not weaken to isPseudo or geometry alone.
Forward direction projects frozen LegalEP clauses. Backward direction must
RECOVER q.ep=some m.dst and opposing flank pawn from actual kernel legality;
do not assume those fields in the right side. No independent seed/clock/count,
ReachK surrogate, new terminal/material/colour/strategy filter or fabricated
compatible history. All q raw flags covered without claiming FIDE admissibility.

A local derivation to audit: isLegal=true implies isPseudo=true. Specialize
source board to some(q.turn,pawn), obtaining pawnMoveOK=true. In pawnMoveOK,
single/double require dx=0, ruled out by distinct files; ordinary capture is
false at empty dst. Thus the existing EP branch holds and supplies raw ep flag
and opposing flank pawn. Preserve the source legality proof throughout. The
exact dx is (dst.file.val:Int)-(src.file.val:Int): prove nonzero using equality
of integer casts, Fin.ext and the distinct-file hypothesis; no coordinate
enumeration or unsupported coercion. Both colours and every legal promotion
field remain covered by the same reasoning.

Use ONE NEW main theorem module, importing frozen RawRepetition.Definitions and
other unchanged dependencies as needed. No new shared definitions are required.
Aggregate imports/AxiomCheck gain additive entries only. Do not inflate with
redundant source/flag/root corollaries. All existing frozen modules stay byte-
identical; corrections only in new modules/version under protocol.

## Adversarial controls and limits

Audit straight single/double pawn moves, ordinary occupied-destination captures,
nonpawn moves, missing/wrong ep marker, wrong flank pawn, both colours, and
pseudo-legal ep which fails self-check. Distinct FILES is not an assumed full
pawn-capture geometry; actual isLegal supplies it. Actual legality cannot be
dropped. Symbolic branch arguments suffice; do not assert concrete pinned or
initial-rooted promotion/ep/castling/threshold histories were constructed/run.
If actual source yields a counterexample/gap, document it and keep candidate
status honest; never silently add missing event fields to the RHS.

This is a kernel event characterization, not ep-normalization preserving all
legal moves, full repetition key/Article9.2.3/rights-history theorem, low-count
certificate, claims/admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK bound, holding/outcome,
DTM/DTZ/WDL/Syzygy or initial-position value. No tablebase/engine/enumeration,
stored certificates, arbitrary-clock KRK witness or novelty claim. No adverse
legal child pruned to manufacture a win.

## Verification and closeout

Run changed module/importers incrementally. Publish proof source BEFORE ONE NEW
GitHub Gate F clone at FULL exact SHA; no .lake before full build, then COMPLETE
AxiomCheck must actually pass. Inspect exact main/axioms (standard-three subsets
only), full logs/commands/exits/timings/UTC, official toolchain identity, all
source/transitive hashes, clean HEAD/tree/status; compare whole working/clean
reports. Gate Z separate: no new frozen row/manifest expected. Preserve every
prior source/paper/audit/evidence/ledger byte; aggregates additive only. No
unrelated diagnostics or new trivial tests.

Update candidate status from actual evidence, roadmap/README, session ledger and
progress table. Write sessions/S046_LEGAL_EP_CHARACTERIZATION.md with complete
observed evidence and FULL installed S047 prompt; consider separate exact-source
freeze before using the result for normalization/key work. Run relevant ledger/
preservation/evidence/document checks; commit/push/merge/push, compare remote
SHAs. Hosted CI unobserved unless actually inspected. Continue installed prompt.

## Cloud activation

Use available runtime guidance, inspect network policy, reuse inherited Git proxy.
Official core Lean4.35.0, no dependency. ELAN_HOME=/workspace/.tools/elan; prepend
bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time, TLS/
checksums unchanged. Existing environment suffices absent actual blocker.
