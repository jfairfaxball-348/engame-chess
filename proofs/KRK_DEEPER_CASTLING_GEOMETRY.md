# KRK: five-ply geometry and exclusion of six-ply castling entries

Locally Lean-verified, unfrozen. Supporting work for strong h=92/93, whose
complete history-aware outcome criterion is still OPEN.

`KRKFourGeometry.framed_shape_sufficient` completes geometric transport in
both directions for a live weak four-ply destination. It maps weak steps and
their exact three-ply child geometry separately; actual flags/history are not
mapped. The existing seventeen-point catalogue therefore supports the pure
clock-free strong five-ply criterion in `KRKFiveGeometry.kernel_five_iff`.
Its conditions are immediate mate, or an edge weak king and an ordinary king
point/rook ray entry into that catalogue, preserving safe rook and nonempty
weak play. It has no future-outcome or legal-move predicate in its formula.

`KRKSixGeometry.kernel_six_iff` expresses nonterminal weak six-ply geometry
as safe rook, at least one coordinate reply, and the explicit five-ply
coordinate test at every guarded neighbour. This finite guard condition is
an intermediate description; a compact destination catalogue for the next
strong band still has to be derived. No complete h=92/93 outcome is claimed.

## Why castling cannot enter a nonterminal six-ply weak win

The five-ply criterion implies an edge weak king. Consequently every interior
neighbour of a weak six-ply root must be covered by the strong king or a rook
line: otherwise that neighbour is an actual legal weak reply, contradicting
the required five-ply child criterion. Safe rook excludes a hidden capture
exception in this argument.

Suppose strong king and rook both occupy rank zero, with the rook on files
2 through 5. If the weak king has positive rank, choose an interior neighbour
whose rank is at least two and whose file differs from the rook file. Such
a neighbour is neither king-controlled nor on a rook line. The proof chooses
its file inward at board boundaries and one file away when it meets the rook;
its rank goes up below rank six and down near the top. All coordinates remain
in 1..6 and all distance/boundary conditions are checked symbolically.
Thus the weak king must lie on rank zero.

At a noncorner square of that rank, the inward neighbour on its file is
uncovered unless the rook shares that file. In that exceptional case choose
the inward neighbour one file away from the strong king; king separation
again leaves it uncovered and its file differs from the rook. Therefore only
a corner is possible. The corner's diagonal interior neighbour then forces
the strong king exactly two files from it: K-file 2 for W-file 0, or K-file 5
for W-file 7. `rank_prison` and `corner_prison` establish these statements.
A reflected coverage argument gives the corresponding home-rank statement
for Black, without reflecting an actual game's flags or trace.

After kingside castling the king is on file 6 and rook on file 5; neither
corner possibility fits. After queenside castling they are on files 2 and 3;
the weak king would have to occupy the original a-file rook square. Actual
`canCastle` requires that square to contain the strong rook, a contradiction.
This proves `castle_not_six` for both colours and arbitrary native flags.

Finally weak seven-ply kernel bounds compress to six by turn parity. The
actual deadline at a nonmating winning child of a strong h>=92 root is at most
seven. Applying the geometric exclusion proves `winning_entry_not_castle`
on the actual admitted appended history. This is a necessary restriction on
all winning entries, not a claim that a chosen ordinary policy is optimal.

Full aggregate build: PASS, 310 jobs. Public axiom audit: PASS; dependencies
are subsets of propext, Classical.choice and Quot.sound. No tablebase, engine,
position atlas, exhaustive position proof, sorry/admit or new axiom was used.
Frozen sources/manifests and the ledger are unchanged.
