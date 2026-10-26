# Corner three-ply witness elimination — unproved next target

**UNPROVED.** For W=(0,0) and distinct pieces with separated kings, the
proposed expansion of the geometric Three predicate is the disjunction of:

1. S.y=2, S.x<=1, R.x>=2 and R.y!=0 (horizontal immediate mate).
2. S.x=2, S.y<=1, R.y>=2 and R.x!=0 (vertical immediate mate).
3. R.x>=3, R.y>=1 and dInf(S,(1,2))=1 (horizontal king entry).
4. R.y>=3, R.x>=1 and dInf(S,(2,1))=1 (vertical king entry).
5. S=(1,2) and [R.x>=3 or (R.y>=1 and (R.y!=2 or R.x>1))].
6. S=(2,1) and [R.y>=3 or (R.x>=1 and (R.x!=2 or R.y>1))].

Rows 5/6 eliminate the rook landing coordinates. In row 5 the allowed
destination rectangle is file>=3, rank>=1. A source already on file>=3 can
move vertically on that file. Otherwise the horizontal crossing to file three
must stay to the right of the king if it shares rank two. Row 6 is its transpose.
Rook safety at the future weak state is automatic because the rook is at least
three squares from the corner. A source coinciding with S must be excluded.

Suggested proof: reduce LastReply at the corner to the two fixed king slots
(1,2) with R.x>=3,R.y>=1, or (2,1) with R.y>=3,R.x>=1. Eliminate the king
landing coordinates, then supply explicit vertical ray or horizontal crossing
witnesses for the two rook rectangles. Compose with the checked strong-three
kernel theorem. No future outcome predicate needs to remain in the formula.

The checked near-corner formula is in `KRKThreePlyNearCorner.lean`. Together
with this corner expansion it will permit direct elimination of every reply
in the four-ply edge conjecture. At W=(2,0), one reply reaches the near-corner
region and admits the extra king entry already identified there; preserve it
in the original-history barrier formula rather than applying the central
rook-only theorem outside its domain.

`python scripts/krk_four_ply_diagnostic.py --corner-three` is a local
falsification diagnostic for this conjecture. It queries no engine/tablebase
and stores no position values. A passed diagnostic is not a theorem.
The executed run checked 3,720 selected roots and found no mismatch.
