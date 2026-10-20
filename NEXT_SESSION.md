# NEXT SESSION — S048: Raw ep-marker irrelevance outside en-passant shape

**Owner instruction:** Prepared handover ONLY. The owner asked to finish S047
and stop. Do NOT start this session automatically. Execute only on a new owner
instruction to resume. Follow AGENTS.md: explicitly fetch ALL remote heads,
merge earlier unmerged work, read latest main prompt, existing checkout/no
worktree. Publication authorised when resumed. Commit/push branch, merge/push
main, compare remote SHAs, never force main. Update/reproduce FULL stable progress
table in closeout/owner report, Syzygy parity LAST, one sentence delta below.
Bundles are not solved material classes.

## Starting point and reading

S047 froze EC-C029 as EC-T0027 at own proof-source
`421608f5b20fee055bc3cb9d0c5904b0d192527b` after NEW exact-source Gate Z.
Read actual EC-T0027 manifest/VERIFICATION-S047 evidence, EC-T0026 event/target
manifest and RawRepetition definitions, EC-C029 paper/audits, Rules.Board dx,
Moves pawnCaptureGeom/pawnMoveOK/isPseudo/canCastle/play/isLegal and updateCastling,
charter/protocol/roadmap/candidates, S046/S047 closeouts and S032 specification.
Twenty-seven bundles frozen; full ep normalization/key/FIDE adjudication open.

## Principal task: smallest ordinary-move prerequisite for normalization

Before attempting the broader effective-ep normalization theorem, prove the
ordinary-move ep-marker irrelevance it needs. Write standalone exact paper and
adversarial audit BEFORE Lean, then register EC-C030 only after fixing a complete
local argument. Add one NEW theorem module, no extra definitions needed; frozen
source unchanged, aggregate imports/runner additive only.

For EVERY raw Position q, actual Move m, and arbitrary e:Option Square, let
r={q with ep:=e}. Under the explicit hypothesis

 ¬(RawClock.Pawn q m ∧ m.src.file≠m.dst.file ∧ q.board m.dst=none),

prove the combined exact statement:

 isPseudo r m = isPseudo q m AND play r m = play q m.

These are Boolean equality and FULL played Position equality, not just board
equality. No actual legality premise is required for these raw non-EP-shaped
moves. Same board/turn/castling, all Move/promotion fields, both colours, arbitrary
raw markers. Do not claim r has a compatible initial-rooted trace or lawful
FIDE history. No clock/count seed or terminal/material/strategy filter.

Audit ALL raw ep uses. play's local epCapture uses exactly source pawn, raw
marker, distinct files and empty dst. Under the hypothesis its capture branch
is false for BOTH markers. Its output ep flag is freshly derived from source
pawn/dy and does not retain the old marker; prove equality of this field too.
All other output fields/arriving promotion/castling effects must be checked.
isPseudo reads ep only through the pawnMoveOK EP branch; if the source is not
q.turn pawn, handle absent/nonpawn/wrong-colour sources and the outer colour
guard precisely. If it IS that pawn, either files coincide (dx=0, capture
geometry false), or destination occupied (EP empty-dst test false). canCastle
and attack tests do not read ep; demonstrate this from actual definitions.
Do not assume pseudo-legality equality from unchanged boards alone.

This selects one missing prerequisite, not an assertion that full normalization
is already proved or falsified. Later normalizeEP(q)={q with ep:=effectiveEP q}
could use this lemma outside the EP shape and frozen legalEP_iff_shape inside
it, but that combined preservation theorem remains a separate obligation.

## Adversarial controls and semantic limits

Audit source absent, wrong-colour pawn, ordinary nonpawn/king/rook/castling,
same-file single/double pawn moves, occupied captures, promotion choices,
source=destination raw moves, both colours and arbitrary malformed ep markers.
Crucially, ¬LegalEP ALONE is NOT this hypothesis: an illegal/pinned EP-shaped
move can still activate total raw play's off-destination removal. Do not weaken
the guard or assume raw play is legality filtered. Use symbolic branch arguments,
not a claim that a concrete pinned or compatible full promotion/ep/castling/
threshold game was run. No coordinate/class enumeration or lookup proof.

The conditional lemma is not reply pruning; every EP-shaped move must remain
covered separately in any later legal-game theorem. No full effective-ep
normalization preservation, repetition key/Article9.2.3/rights-history theorem,
low-count certificate, claims/admissibility/adjudication/mate precedence, full
Layer/strategy extraction/lifting, numerical KRK bound, holding/outcome,
DTM/DTZ/WDL/Syzygy or initial-position result. Classical kernel reasoning,
no novelty/tablebase/engine/stored certificates/arbitrary-clock KRK witness.

## Verification and closeout

Run changed module/importers incrementally. Publish proof source BEFORE ONE NEW
GitHub Gate F clone at FULL exact SHA; no .lake before full build, then COMPLETE
AxiomCheck must actually pass. Inspect exact main/axioms (standard-three subsets
only), retain full logs/commands/exits/timings/UTC, official toolchain, all source/
transitive hashes, clean HEAD/tree/status; compare whole working/clean output.
Gate Z separate: no frozen row/manifest this session. Preserve every prior
source/paper/audit/evidence/ledger byte; aggregates additive only. No unrelated
diagnostics or trivial tests. If a gap/counterexample appears, record it honestly,
not a weakened or fabricated successful statement.

Update candidate/roadmap/README/session ledger/progress table. Write
sessions/S048_ORDINARY_EP_IRRELEVANCE.md with complete actual evidence and FULL
installed S049 prompt. Consider separate exact-source freeze before broader
normalization. Run relevant ledger/evidence/preservation/document checks,
commit/push/merge/push and compare remote SHAs; hosted CI unobserved unless
actually inspected. Stop at closeout unless the owner explicitly authorises
further consecutive sessions again.

## Cloud activation

Use available runtime guidance, inspect network policy, reuse inherited Git proxy.
Official core Lean4.35.0, no dependency. ELAN_HOME=/workspace/.tools/elan; prepend
bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time, TLS/
checksums unchanged. Existing environment suffices absent actual blocker.
