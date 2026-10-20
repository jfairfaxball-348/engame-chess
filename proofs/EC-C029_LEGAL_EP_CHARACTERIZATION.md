# EC-C029 — Kernel characterization of the actual legal en-passant event

S046, 2026-10-20. Classical case analysis of the unchanged legal-move kernel,
no novelty claim. Sources: frozen Rules.Board dx and finite-square coordinates,
Moves isLegal/isPseudo/pawnMoveOK, RawClock.Pawn and EC-T0026 LegalEP definition.
No engine/tablebase/coordinate enumeration or stored-position certificate.

## Exact universal statement

For EVERY raw Position q and actual Move m (including its promotion field):

    LegalEP q m ↔ isLegal q m=true ∧ RawClock.Pawn q m ∧
      m.src.file≠m.dst.file ∧ q.board m.dst=none.

LegalEP is FROZEN: actual isLegal, source q.turn pawn, raw ep flag matching dst,
distinct files, empty dst and opposing flank pawn. The right side deliberately
DOES NOT assume raw ep equality or flank pawn. They must be recovered from
actual legality. No history/clock/count seed, arbitrary KRK prefix, erased-history
surrogate, terminal/material/colour/strategy filter or FIDE-admissibility premise.
All raw flags and both colours; invalid raw flags are not certified lawful.

## Proof

Forward: project LegalEP's legal/source-pawn/distinct-file/empty-dst clauses.

Backward: fix the four right-side facts. Let fsrc,fdst be Fin 8 file values.
The actual dx(src,dst) is (fdst.val:Int)-(fsrc.val:Int). If dx=0 then the integer
casts agree, hence natural values agree and Fin.ext gives fdst=fsrc, contrary
to distinct files. Thus dx≠0. This is injectivity/arithmetic, not enumeration
of coordinates and not an assumption of full pawn-capture geometry.

isLegal=true implies isPseudo=true by its Boolean conjunction. Specialize the
source board using Pawn: the source is exactly (q.turn,pawn). The pawn branch
of isPseudo therefore supplies pawnMoveOK=true (and promotion validity, which
is retained through the ORIGINAL isLegal premise).

The single and double branches of pawnMoveOK each require dx==0, so both are
false. The ordinary-capture branch matches an occupied destination, so it is
false because dst is empty. The only remaining disjunct is the existing EP
branch. Its Boolean conjunction supplies pawnCaptureGeom, q.ep==some m.dst,
empty destination and opposing flank pawn. Correct equality tests give the
propositional raw ep/flank equations. Together with original legality, Pawn,
distinct files and empty dst they form EXACTLY frozen LegalEP. No field was
silently added to the right side, nor legality weakened to pseudo-legality.

One new main theorem module suffices; no new definitions or elementary
corollary modules. All frozen definitions/proofs imported unchanged.

## Adversarial controls

Straight single/double pawn moves fail distinct files. Ordinary pawn captures
fail empty dst. Nonpawn moves fail Pawn even if their destination is empty and
file changes. Missing/wrong ep marker or opposing flank pawn prevents the only
remaining pawnMoveOK branch from holding, so no such RHS can be actually legal.
Both colours use their existing forward direction and actual legality; proof
eliminates alternatives without assuming white/black-specific ranks. A merely
pseudo-legal ep that exposes its own king is excluded by actual isLegal; the
theorem never substitutes isPseudo for that premise. Every promotion field
remains checked by original legality, even for malformed raw flags.
Controls are symbolic branch implications; no concrete pinned or compatible
full initial-rooted promotion/ep/castling/threshold game was run or asserted.

## Limits

This validates the kernel event boundary; it is not a theorem that ep-field
normalization preserves every legal move/played endpoint. No full repetition
key/Article9.2.3/rights-history correspondence, low-count certificate, claims/
no-earlier-terminal admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK mate bound, holding/outcome,
DTM/DTZ/WDL/Syzygy parity or initial-position value. Existing owner-reviewed
FIDE-to-kernel encoding remains trusted; no new English-law correspondence.
No adverse legal reply pruned, new solved class or frozen row follows.
