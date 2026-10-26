# A coordinate-only three-ply formula on a central edge

For W=(x,0), 2<=x<=5, and distinct S,R, define F-=x-1 and F+=x+1.
The checked Three region is exactly the disjunction of the following five
coordinate rows. No landing-square witness remains.

| Type | Coordinate condition |
|---|---|
| Immediate mate | S=(x,2), R.y!=0, and abs(R.x-x)>=2 |
| King entry from the right | R.y>=2, R.x=F-, and dInf(S,(F+,2))=1 |
| King entry from the left | R.y>=2, R.x=F+, and dInf(S,(F-,2))=1 |
| Rook entry with S=(F+,2) | R.x=F-, or R.y>=3, or R.y=2 and R.x<S.x |
| Rook entry with S=(F-,2) | R.x=F+, or R.y>=3, or R.y=2 and S.x<R.x |

On an exact strong-turn kernel board with separated kings and no existing
check on the weak king, Three is already proved equivalent to mate within
three plies. Thus the table evaluates that outcome on legal strong arrivals.
It does not remove incoming-history barriers or classify all KRK positions.

## Elimination argument

The last-reply formula on this central edge reduces to S.y=2, R.y>=2, and
either S.x=F+,R.x=F- or S.x=F-,R.x=F+. The rank-one rook alternative is
excluded by safety: its file is adjacent to W while the protecting king is
two files away. Corner exceptions do not occur when 2<=x<=5.

Consequently the possible king landing squares are exactly (F+,2) and
(F-,2), giving the second and third rows.

For a rook entry the required destination file is fixed. A rook already on
that file has a free vertical ray: neither king occupies it. Rank six or seven,
chosen to differ from the source, supplies an explicit safe landing square.
Otherwise the destination must be the crossing of that file with the rook's
current rank. At rank three or above neither king blocks it. On rank two the
crossing must remain on the same side of S. A source coinciding with S is
excluded by distinctness. These are the last two rows, with matching necessity.

## Lean correspondence and checks

`KRKThreePlyMiddle.lean` defines MiddleThree and proves last_middle_iff,
immediate_middle_iff, king_entry_middle_iff, rook_entry_middle_iff, and
three_middle_iff. The focused build
`lake build EndgameChess.Rules.KRKThreePlyMiddle` passed. The separate local
diagnostic `python scripts/krk_four_ply_diagnostic.py --middle-three` checked
14,384 selected roots without mismatch; the Lean proof supplies universal
validity under the stated hypotheses.

The aggregate `lake build` passed (263 jobs) and `lake env lean AxiomCheck.lean`
passed. The new public declarations use only `propext`, `Classical.choice`,
and `Quot.sound`.
