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
