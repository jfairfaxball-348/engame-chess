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
