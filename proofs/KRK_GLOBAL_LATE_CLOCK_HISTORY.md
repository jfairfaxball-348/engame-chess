# KRK: all-orientation late-clock RAW history criteria

Locally Lean-verified, unfrozen. KRK remains OPEN. No tablebase or engine values are used.

## Exact domain and conclusion

Let `s` be an admitted RAW trace whose current board is exact KRK, with strong
colour sigma and coordinates K, R, W. Assume the current state is ongoing.
For strong turns with h >= 96, `KRKFramedHistory.GlobalClear` is equivalent to
forced mate and to `ActualWin`. For weak turns with h >= 95,
`KRKGlobalWeakBand.Clear` has those equivalences. Both statements quantify over
both colours, every board orientation and every admitted incoming trace, with
actual flags and actual legal moves. No rights-clearing hypothesis is added.

In each domain the complement is equivalent to weak holding and to holding by
both players. Exact minimum winning ply bounds are 1/3 on strong turns (split
by `MateNow`) and 2/4 on weak turns (split by `LastReply`). Here distance means
the smallest bound in the checked `W` mate-within semantics; this is not a claim
of global Syzygy DTZ correspondence.

## Coordinate normalization, not history normalization

A `Frame` has mutually inverse coordinate maps f and r, preserving Chebyshev
distance, rook visibility, immediate-mate geometry and last-reply geometry.
Composition allows rotations as well as involutive reflections. `normalize W`
sends any edge square to (x,0), 0 <= x <= 3: map its edge to the bottom, then
reflect files when needed. Non-edge squares fail the strong criterion.

The geometry invariance proofs use synthetic castling-free boards to connect
the previously checked kernel geometry and certified board isometries. These
synthetic boards are proof objects only. We do not transform an actual RAW
trace, repetition key, castling flag or clock. Every candidate entry destination
is pulled back with r; `play` and all occurrence queries remain native.

## Seven canonical last-reply slots

All coordinates below are normalized; all inequalities are ordinary integers.
The table exhausts `LastReply` at W=(x,0), 0 <= x <= 3. K is the strong king
*after* an entry, R its rook, and U is the unique subsequent weak reply.

| Weak file | Slot | K | R region | U |
| --- | --- | --- | --- | --- |
| 0 | cornerRank | (1,2) | R.x >= 3, R.y >= 1 | (1,0) |
| 0 | cornerFile | (2,1) | R.x >= 1, R.y >= 3 | (0,1) |
| 1 | nearEast | (2,2) | R.x=0, R.y>=2 | (2,0) |
| 1 | nearWest | (0,2) | R.x=2, R.y>=2 | (0,0) |
| 1 | nearInner | (1,2) | R.x=2, R.y>=1 | (0,0) |
| 2 or 3 | middleEast | (x+1,2) | R.x=x-1, R.y>=2 | (x+1,0) |
| 2 or 3 | middleWest | (x-1,2) | R.x=x+1, R.y>=2 | (x-1,0) |

`last_catalogue_iff` proves both directions using the existing corner, near
and middle geometry. Slot validity supplies distinct kings/rook, king distance
at least two, an actual model step to U, and rook coordinates off W and U.
No coordinate arithmetic wraps at board boundaries.

## Strong-turn formula

Write g=normalize W. `GlobalClear` requires depth(W)=0 and one of:

1. The checked immediate-mate coordinate/rook-clearance test at fK,fR,fW.
2. A valid slot whose rook region contains fR, with dInf(fK,slotK)=1,
   and `EntryClear` for the native king move K -> r(slotK) followed by
   W -> r(U).
3. A valid slot with fK=slotK, and a rook destination on one of the two
   lines through fR satisfying its region and clearance inequalities,
   with `EntryClear` for the native rook move and native reply.

The ray test requires a changed destination coordinate and excludes the strong
king strictly between source and destination. The region excludes weak-king
blocking. It is exactly rook visibility, proved by `ray_sees_iff`.

`EntryClear` is h<98 and both native entry/reply result keys having fewer than
two occurrences in the incoming trace. Mate leaves retain mate precedence.
The previously checked full three-ply theorem handles all other strong legal
alternatives, including castling. The present proof eliminates its remaining
entry geometry and unique-reply existential using the seven slots. It does not
assume reflected flags make an equivalent actual game.

## Weak-turn formula in the original trace

Require safe rook, h<99 and fewer than three current occurrences. For every
square T satisfying the explicit neighbour guard

    dInf(W,T)=1, T != R, dInf(K,T)>=2, not RookSees(R,T,K,T),

require (a) fewer than two original occurrences of the actual first-move
result, (b) depth(T)=0, and (c) the framed strong formula at T, with each
`EntryClear` replaced by `OriginalEntry`:

    h<97,
    occurrences(original trace, play(firstBoard,M))<2,
    occurrences(original trace, play(play(firstBoard,M),T->U))<2.

The universal coordinate guard has at most eight surviving squares; the
inner formula uses seven slot kinds, two rook-line axes and eight coordinates.
There are no legal-move or future-outcome predicates in the evaluated tests.
This is not a recursive value definition.

`KRKFramedPrefix` proves the replacement exactly: the first quiet weak append
contributes zero to the entry query (opposite turn) and reply query (different
weak king). It verifies actual legality/material and the unique native reply
for each point/ray before applying `KRKWeakPrefixEntry.entry_append_iff`.
Necessity uses all actual weak branches and the exact strong >=96 theorem;
sufficiency verifies current/intended claim absence and a uniform three-ply
certificate at every actual child. Ongoing admission supplies nonempty play,
so universal branch conditions cannot certify stalemate by vacuity.

## Verification and remaining scope

`lake build`: PASS, 296 jobs. `lake env lean AxiomCheck.lean`: PASS. All new
public theorem declarations are included; reported axioms are subsets of
propext, Classical.choice and Quot.sound. No sorry, admit or new axiom.

These results extend the previously checked bottom-edge families to all
orientations. They do not settle strong h=94/95, lower positive clocks, all
terminal/capture cases, full FIDE repetition correspondence or global WDL/DTZ.
Historical frozen modules/manifests and the theorem ledger are unchanged.
