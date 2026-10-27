# Complete near-corner strong three-ply history formula

Status: locally Lean-checked, unfrozen. Exact RAW outcome in the stated
band, for either strong colour; not complete KRK closure.

Assume an ongoing admitted RAW KRK history H, strong turn, W=(1,0), and
halfmove clock h>=96. The strong side wins exactly when immediate mate is
available or one of the following finite point/interval tests passes.
No restriction on the strong king or rook beyond exact admitted KRK is
added to this domain.

| Slot | King square K | Rook file f | Minimum rook rank b | Forced weak destination U |
|---|---|---|---|---|
| East | (2,2) | 0 | 2 | (2,0) |
| West | (0,2) | 2 | 2 | (0,0) |
| Inner | (1,2) | 2 | 1 | (0,0) |

Coordinates are zero-based. Immediate mate is precisely S=(1,2), R.y!=0,
and R.x>=3. Its winning distance is one ply.

For a **king point**, require R.x=f, R.y>=b, and dInf(S,K)=1. Play the
actual canonical king move S->K, then the forced weak move W->U. Require
h<98 and fewer than two occurrences in H of each resulting position key.
There are exactly three candidate king points in the table.

For a **rook interval**, require S=K and a rank y in [b,7]. Its actual
rook destination is (f,y). The allowed source/destination conditions are:

* R.x=f and R.y!=y, giving a vertical move; or
* R.x!=f, R.y=y, and, if R.y=2, K.x does not lie strictly between R.x and f.

These are explicit linear coordinate conditions. The king cannot block
a vertical move on f, and W cannot block either allowed move. For this
rook move and its forced weak reply W->U, again require h<98 and fewer
than two occurrences of both resulting keys in the original H. The only
quantified destination is one rank in a fixed interval; no legal-move or
future-outcome predicate remains in the test.

If neither immediate mate nor a clear point/interval exists, the weak
side has a holding policy against every strong alternative. Whenever a
win exists without immediate mate, its exact rule-game mate distance is
three plies; winning within two is impossible.

## Proof correspondence

`last_slots_iff` evaluates LastReply as exactly the three table rows.
Every actual king entry must reach one listed K, and every rook entry
must place the rook on the corresponding f at a rank at least b.
`slot_sees_iff` eliminates the rook-line and blocking predicates into the
displayed source/destination conditions. A direct legal weak-return proof
and the unique-reply theorem identify U, including the protected rank-one
inner slot. Canonical actual king/rook legality is constructed, retaining
the incoming flags. The full three-ply history theorem supplies necessity
against all actual strong alternatives, including castling exclusion.

The source is `KRKNearSlotBarriers.lean`: `KingPoints`, `AllowedRank`,
`RookStrips`, `NearClear`, `high_clock_force_iff`,
`high_clock_actual_iff`, `high_clock_hold_iff`, and
`high_clock_distance_cases`.

## Carrying an entry back through an initial weak move

`KRKWeakPrefixEntry.lean` proves a general original-history identity for
any safe-rook weak root, actual first weak move W->T, actual strong entry
M reaching LastReply, and its actual weak reply T->U. The first append
adds no occurrence to either later queried key. The strong-entry key has
the opposite turn; the following key has a different weak king square
because the actual weak reply moves that king. Thus EntryClear after the
first weak move is exactly h<97 and the two later key counts below two in
the original root trace.

This identity uses actual positions and normalized keys, with no symmetry
of incoming histories assumed. It removes the need to reprove a separate
key-update lemma for each point or interval. It does not itself classify
the weak root: all its legal replies, root claims, terminal/capture cases,
and a matching complete board region must still be handled.

The remaining corner and transposed near-corner strong formulas, the
W=(1,0)/(0,0) weak history bands, lower clocks, full FIDE correspondence
and global WDL/DTZ distances remain open.
