# KRK: exact interior six-ply geometry and a stronger RAW drawing region

Locally Lean-verified, unfrozen. Full KRK remains OPEN.

## Complete clock-free interior criterion

For every exact KRK kernel board with weak side to move, separated kings and
an interior weak king, mate within six plies holds exactly as follows.
The weak king must be one of (1,1), (1,6), (6,1), (6,6). Reflect coordinates to
send that square to W=(1,1). In that frame, the only winning families are:

- K=(3,1), R.y=2 and R.x>=3;
- K=(1,3), R.x=2 and R.y>=3.

All such boards have exact minimum kernel mate-within bound six: the previous
interior lower bound excludes five. `KRKSixInwardCorner.global_kernel_six_iff`
and `global_kernel_exact_six` prove these statements for both strong colours.
The reflections act on geometry only; no actual flags or trace are reflected.
These are kernel DTM statements, not unqualified history-aware wins.

## Near-corner five-ply formula used by the proof

For W=(1,0), legal strong-arrival geometry, `KRKFiveNear.kernel_five_iff`
evaluates five-ply mate by three king-entry tests and three rook alternatives.
The king entries are a king step to the following destination with its region:

| Destination | Rook region |
| --- | --- |
| (0,2) | R.x=2, R.y>=2 |
| (1,2) | R.y>=3, or R.y=2 and R.x>=2, or R.y=1 and R.x in {2,3} |
| (2,2) | R.x=0 and R.y>=2, or R.x>=3 with R!=(3,1) |

The rook alternatives are K=(1,2), K=(2,2), or K=(0,2) with R.x=2 or R.y>=2.
There is no moved-square search in these tests. Actual immediate mate is
already contained in K=(1,2). Each destination has checked safe-rook,
distinct-piece and live-reply geometry. For K=(2,2), the rook can always reach
either its left-file region or right-hand region: the proof distinguishes
file zero, the exceptional source (1,2), and a move to file four/five.
Source king/rook and rook/weak-king distinctions prevent blocking exceptions.

## Interior proof

The earlier strip/deep coverage exclusions leave only four inward-corner
weak squares. At W=(1,1), inward-neighbour coverage restricts the strong pieces
to the five previously checked corner-prison families. In the horizontal
family K.x=3, K.y<=2, R.y=2, safe rook implies R.x>=2. The actual south reply
(1,0) and the exact near-corner five-ply test force K.y>=1 and R.x>=3.
K.y=2 is excluded by the additional actual reply (2,0), whose middle five-ply
rank-two criterion fails. This leaves exactly K=(3,1), R.x>=3, R.y=2.
The transpose gives the second family.

The two other wall families admit an outward upper reply which, after axis
swap, has strong king rank three and rook rank one. The exact low-rook middle
five-ply criterion requires king rank two, so these cannot force in six.
The remaining diagonal prison K=(3,3), R=(2,2) has an actual reply (0,0)
outside every five-ply destination slot. All these exclusions are symbolic
geometry arguments, not a position-value table.

For sufficiency in the horizontal family, every actual weak geometric reply
is one of (0,0), (0,1), (1,0). Each has a checked king entry into a four-ply
region; the vertical family follows by axis swap. Safe rook and at least one
legal reply are proved explicitly, so captures and stalemate are not pruned
or promoted to wins. The complete six-ply kernel theorem then applies.

## New full-history RAW drawing region at h>=92

`KRKSixInteriorHolding.high_clock_interior_holding` proves both-player holding
and absence of `ActualWin` on every admitted RAW KRK history with:

- strong side to move;
- h>=92;
- an interior weak king outside those four inward-corner squares.

The exact deadline gives a kernel bound at most eight. Any nonterminal strong
first move, including castling, preserves the weak square and reaches a weak
seven-ply bound; parity compresses that to six. The complete interior six-ply
necessity above excludes the original weak square. Immediate mate is also
impossible in the interior. Thus no actual forcing certificate exists,
independently of incoming repetition history. Existing holding duality and
strong nonloss provide the two actual RAW holding strategies.

This extends the earlier interior strong h>=94 draw exclusion to h=92/93
outside four squares. It does not settle those four squares' history barriers,
edge outcomes at the new band, lower clocks, full FIDE correspondence or
global rule-aware DTM/DTZ.

Full aggregate build: PASS, 316 jobs. Public axiom audit: PASS, all new public
main declarations included. Dependencies are subsets of propext,
Classical.choice and Quot.sound. No sorry/admit/new axiom/unsafe escape,
tablebase, engine or stored position values. Historical frozen evidence and
the ledger remain unchanged.
