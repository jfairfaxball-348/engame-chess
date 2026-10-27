# KRK: complete strong-turn RAW history band h >= 94

Locally Lean-verified, unfrozen. This extends the [all-orientation late-clock
criteria](KRK_GLOBAL_LATE_CLOCK_HISTORY.md); full KRK remains OPEN.

## Statement

For every admitted, ongoing exact KRK RAW history, both strong colours and
all board orientations, with strong side to move and halfmove clock h >= 94,
`KRKFivePlyHistory.Clear` is equivalent to forced mate and `ActualWin`.
Its complement is equivalent to weak holding and to both-player holding.
Winning positions have exact minimum mate-within bounds one, three or five
board plies. The one-ply test is `MateNow`; the three-ply test is the explicit
`KRKFramedHistory.GlobalClear`. The remaining winning positions require five.
No generic outcome recurrence, tablebase, engine or position atlas is used.
These statements concern the RAW rule layer, not completed FIDE/DTZ parity.

## Exhaustive nonmating destinations

Any winning nonmating first move reaches a weak turn with clock at least 95.
The exact deadline is at most five board plies there; weak-turn parity reduces
its clock-free projection to four. The weak king must lie on an edge, by the
checked interior four-ply lower bound.

Normalize this edge square to W=(x,0), 0<=x<=3, using coordinates only. The
complete nonterminal weak four-ply destination catalogue is below. Coordinates
K and R refer to the board *after* the first strong move.

| x | K | R condition |
| --- | --- | --- |
| 0 | (0,2) | R.y>=2 or R.x=2 |
| 0 | (2,0) | R.x>=2 or R.y=2 |
| 0 | (1,2) | R.y>=1 |
| 0 | (2,1) | R.x>=1 |
| 0 | (2,2) | (R.x>=3 and R.y>=3), or (R.x=0 and R.y>=2), or (R.y=0 and R.x>=2), or R=(1,2), or R=(2,1) |
| 0 | (a,3), a=0,1,2 | R=(2,1) |
| 0 | (3,a), a=0,1,2 | R=(1,2) |
| 1 | (0,2) | R.x=2 and R.y>=2 |
| 1 | (1,2) | R.y>=3, or (R.y=2 and R.x>=2), or (R.y=1 and R.x in {2,3}) |
| 1 | (2,2) | (R.x=0 and R.y>=2), or (R.x>=3 and R!=(3,1)) |
| 2,3 | (x-1,2) | R.x=x+1 and R.y>=2 |
| 2,3 | (x,2) | R.y>=3 |
| 2,3 | (x+1,2) | R.x=x-1 and R.y>=2 |

There are eleven corner points, three near-corner points and three middle
points. `KRKFourSlots.shape_iff` proves that their union is exactly the checked
canonical four-ply geometric region. Distinct-piece and live-reply tests are
retained separately; this table alone is not a history-aware win assertion.

`KRKFourGeometry` transfers the weak reply geometry and complete three-ply
child geometry to the coordinate frame. Its synthetic boards carry no actual
history. This establishes the necessary destination shape without transporting
actual castling rights or repetition keys.

Castling is eliminated as a first entry by an additional argument, not by an
assumption about rights. Kingside castling's resulting K/R placement misses
all four-ply regions. A queenside placement can fit only when the weak king is
on the original a-file rook square, contradicting the actual required rook
occupancy. `KRKCastleFour.castle_not_four` checks both colours and actual
castling conditions. Consequently every nonmating entry is an ordinary king
step or rook relocation (`four_entry_move`). Immediate mate is handled by the
existing exact mating-source theorem.

## Original-history barrier formula

Let the native first strong move be M, P=play(root,M), and H the original
trace. For any queried position Q define

    C_M(Q) = occurrences(H,Q) + [key(P)=key(Q)].

The indicator is retained even when it could be simplified. It accounts for
exactly the appended P, with its actual flags; no key equality is guessed from
piece coordinates. `KRKStrongPrefix.occurrences_append` proves the identity.
All strong KRK moves are quiet in this model, so the child clock is h+1.

For a candidate post-entry K/R placement, `WeakAfter` requires:

- a safe rook, h<98 and occurrences(H,P)<2;
- for each explicitly guarded weak neighbour T, C_M(play(P,W->T))<2,
  depth(T)=0 and the seven-slot framed strong formula at T;
- in that inner formula, each two-key entry test is evaluated as h<96 and
  C_M(Q_entry)<2, C_M(Q_reply)<2, using actual native `play` throughout.

The neighbour guard is dInf(W,T)=1, T!=R, dInf(K,T)>=2 and absence of rook
attack at T. It selects at most eight squares. A separate existential guard
requires at least one actual reply: stalemate cannot satisfy a universal test
vacuously. The inner immediate-mate alternative retains mate precedence.
`weak_append_iff` proves exact correspondence with the checked global weak
>=95 formula on the actual appended trace.

The final strong formula is immediate mate, or an edge W and one of:

1. A catalogue king point adjacent to the old king, with the unchanged rook
   in its region, kings separated, pieces distinct, a live weak reply and
   `WeakAfter` for the native king move to the inverse-frame point.
2. A catalogue point already occupied by the strong king, with a destination
   on a rook line through the old rook and in that point's rook region,
   distinct pieces, a live weak reply and `WeakAfter` for that native rook move.

These tests contain only finite point/line/clearance conditions, native play
and old-key counts. They contain neither legal-move tests nor future outcomes.
The ordinary-move legality lemmas verify sufficiency without a rights-clearing
hypothesis. A live reply and the evaluated tests establish child ongoing,
nondead status and all current/intended claim exclusions before the four-ply
weak certificate is applied.

## Necessity, holding and exact distances

Necessity considers every legal strong move of a forcing certificate. Terminal
winning children give the exact immediate-mate branch. All other winning
children obey the deadline, destination catalogue, castling exclusion and full
weak history criterion above. Therefore failure of every finite entry is a
proved absence of forcing, and holding duality supplies the defender policy.
Strong nonloss was already proved for every admitted KRK history.

`KRKThreePlyExact` separately establishes the exact three-ply coordinate/history
criterion at every clock. `KRKDistanceParity` checks compression of strong
four-ply rule certificates to three, preserving actual claims/admission. Thus
failure of the three-ply test excludes every four-ply certificate. Together
with the five-ply sufficiency theorem this proves the stated exact distance
split, rather than only another upper bound.

## Verification and remaining scope

Full `lake build`: PASS, 304 jobs. `lake env lean AxiomCheck.lean`: PASS, with
all new public theorem declarations audited. Dependencies use only subsets
of propext, Classical.choice and Quot.sound. No sorry/admit/new axiom or unsafe
escape was introduced. Historical frozen sources, manifests and ledger remain
unchanged. No hosted CI or Palomar result is asserted.

Next: weak h=93/94, strong h<=93 and lower clocks, then complete terminal/capture
coverage, full FIDE correspondence and global WDL/DTZ. This exact higher-clock
band does not close those obligations or the full material class.
