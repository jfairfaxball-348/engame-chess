# S036 — adversarial paper review of EC-C024

Saved BEFORE Lean. Same-agent review, not independent external review.
The exact statement in proofs/EC-C024_RAW_HALFMOVE_FOLD.md has no local gap.

| Attempted falsification | Resolution |
|---|---|
| Occupied dst may be friendly | Legal premise supplies targetOK; enemy and nonking follow. Raw Boolean occupancy is not called a capture off that domain. |
| En passant lands on empty dst | Pawn branch resets. EPCapture explicitly records opposing flank pawn and ep geometry/flag; no material-count equivalence is claimed. |
| Promotion moves a queen | Source, rather than arriving kind, determines Pawn. All promotion choices reset. |
| Castle moves rook / loses rights, so reset | Source king and empty dst imply nonzeroing; canCastle branches explicitly prove empty dst. Rights changes do not occur in detector. |
| Nonpawn captures away from dst | Kernel play's only extra capture branch requires source pawn; castles relocate their own rook. |
| Empty root has one position | Counter bounds move length (zero), not position length (one). |
| Zeroing loses earlier repetition evidence | Fold never modifies Trace. Frozen append_spec retains all prefixes. |
| Arbitrary clock assigned to KRK | Counter recurses from initial trace root zero; no seed parameter. |
| Draw-ending replies pruned | No change to RawBoardStep, no Ongoing guard; raw continuation retained. |
| Clock bound proves sub-100 mate budget | Rejected: history length is not a uniform future mating bound. |
| Per-case lemma replaces general proof | Structural induction covers every stored trace; event equivalence quantifies over every kernel-legal move. |

Control arguments for singles/doubles, capture, promotion, ep, quiet king/rook
and castle are symbolic; no fixed game prefix or diagnostic is reported as run.
Kernel event correspondence is explicit; English FIDE encoding remains the
existing trusted bridge, and material-count equivalence is not claimed.
Verdict: LOCAL_VERIFIED for exact raw-counter statements; Gate F pending.
