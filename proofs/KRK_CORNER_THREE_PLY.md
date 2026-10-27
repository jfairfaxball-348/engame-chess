# Exact corner three-ply formula

Status: locally Lean-checked, unfrozen. This is a kernel geometry result,
not full KRK history-aware closure.

Use zero-based coordinates. Let W=(0,0), let S be the strong king and R
its rook, and assume S differs from R. The geometric predicate `Three`
is equivalent to the following six-row disjunction:

| Row | Conditions |
|---|---|
| Horizontal immediate mate | S.y=2, S.x<=1, R.x>=2, R.y!=0 |
| Vertical immediate mate | S.x=2, S.y<=1, R.y>=2, R.x!=0 |
| Horizontal king entry | R.x>=3, R.y>=1, dInf(S,(1,2))=1 |
| Vertical king entry | R.y>=3, R.x>=1, dInf(S,(2,1))=1 |
| Horizontal rook entry | S=(1,2), and R.x>=3 or [R.y>=1 and (R.y!=2 or R.x>1)] |
| Vertical rook entry | S=(2,1), and R.y>=3 or [R.x>=1 and (R.x!=2 or R.y>1)] |

The brackets in each rook row belong to the condition following its fixed
king square. For exact KRK with strong turn, separated kings and no current
rook check of W, the existing `strong_three_iff` identifies `Three` with
kernel mate within three plies. No history transformation is used here.

The proof first evaluates `LastReply`: the horizontal king slot is (1,2)
with destination rook file at least three and rank at least one; the
vertical slot is the transpose. These slots directly eliminate the king
entry witnesses. For rook entries, a source already inside the permitted
file strip has a distinct vertical destination at rank six or seven.
Otherwise a horizontal move to file three is possible precisely when
the king does not block it. The vertical row uses the transposed argument.

The correspondence is in `formal/EndgameChess/Rules/KRKThreePlyCorner.lean`:
`last_corner_iff`, `immediate_corner_iff`, `king_entry_corner_iff`,
`rook_entry_corner_iff`, and `three_corner_iff`. All landing squares are
constructed geometrically; no position-value enumeration is used.

The fixed original-history barriers for nonmating entries remain necessary
when applying this geometry to RAW outcomes. These coordinate identities
alone do not establish those outcomes, FIDE correspondence or global distance.
