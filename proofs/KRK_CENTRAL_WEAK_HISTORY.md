# Complete RAW weak-turn late-clock formula on the two middle bottom files

For an ongoing admitted exact KRK history H with W=(x,0), 3<=x<=4, the weak
side to move, and halfmove clock h>=95, the strong-side winning criterion is
now evaluated in the original incoming trace. Both colours are quantified.
This result covers these two bottom-edge files; other edge files/orientations,
earlier clocks, global distances and full FIDE correspondence remain open.

There are exactly two disjoint winning families.

## LastReply: exact distance two

Require the checked coordinate predicate LastReply(S,R,W), together with

    h<99,    c_H(q)<3,    c_H(play(q,(W,(S.x,0),none)))<2.

The displayed weak move is the unique actual legal reply in this region.
These inequalities evaluate all current and intended claim possibilities.

## Direct opposition: exact distance four

Require S=(x,2), R.y>=3, h<97 and c_H(q)<3. The two possible weak moves are
to L=(x-1,0) and U=(x+1,0). L is legal exactly when R.x!=x-1; U is legal
exactly when R.x!=x+1. At least one is legal. For **each legal branch** t:

* The first child q1=play(q,(W,t,none)) has c_H(q1)<2.
* After L the rook landing file is f=x-2; after U it is f=x+2.
* There exists a rank y in 2..7 satisfying the complete ray condition:
  if R.x=f then y!=R.y; otherwise y=R.y.
* For m=(R,(f,y),none), let q2=play(q1,m) and
  q3=play(q2,(t,(S.x,0),none)). Require c_H(q2)<2 and c_H(q3)<2.

All three branch queries are in H, before the first weak move. The attacker
may choose different ranks on the two defender branches. No common-rank
assumption is inserted.

## Why no history information is lost

The first append adds the strong-turn key q1. The later q2 has weak turn,
so its key differs from q1. The later q3 has weak king back on the original
file x, whereas q1 has weak king at x-1 or x+1. Its normalized key also
differs from q1. Thus neither later count changes when q1 is appended.
Castling rights and effective en-passant data are still updated by actual
kernel play; no history is transformed, pruned, or reset.

Current count at q must be below three. Every actual intended first weak
move must lead to an old key count below two. These conditions are independent
of the two later ray barriers and are retained explicitly. Numeric bounds and
the board mating certificates establish ongoingness at all intermediate
states, including every legal defender reply. Final mate is accepted with
the existing mate precedence.

## Necessity, sufficiency and distances

The exact clock deadline limits a weak root with h>=95 to at most five plies.
Turn parity reduces five to four. The complete middle-file four-ply board
classification leaves only LastReply or opposition, since the root is ongoing.
The unique-reply claim test gives the first family. The complete strong
rook-ray theorem applies to every legal child in the second family and gives
its necessary and sufficient interval conditions.

Conversely the displayed counts exclude every current/intended defender claim,
and each legal branch admits its own checked three-ply certificate. This gives
a four-ply certificate on the same admitted trace. A failed formula gives a
defender holding policy against every strong alternative. The strong side
already has a universal KRK holding policy, so failure characterizes the
region where both players can hold in the RAW layer.

The winning distance is two in LastReply; one ply is impossible at an ongoing
weak root. In opposition, distance four is attained and distance at most three
is impossible because LastReply is disjoint from S.x=W.x. The public distance
theorem exposes both cases.

## Lean correspondence and executed checks

`KRKOppositionPrefix.lean` proves weak-king key separation and unchanged
occurrence queries across the first append. `KRKOppositionHistory.lean`
defines OppositionClear and proves its forcing, actual-win, holding and exact
four-ply characterisations. `KRKCentralWeakBand.lean` defines CentralClear and
proves the combined forcing, actual-win, holding, drawing and distance cases.

`lake build` passed (267 jobs). `lake env lean AxiomCheck.lean` passed, with
only `propext`, `Classical.choice`, and `Quot.sound` for the new public
declarations. No engine, tablebase, enumerated value table or diagnostic
computation supplies the proof. Existing frozen sources/manifests are retained.
