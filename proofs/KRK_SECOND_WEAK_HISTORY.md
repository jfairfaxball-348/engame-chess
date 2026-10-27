# Complete weak W=(2,0) late-clock classification

Status: locally Lean-checked, unfrozen. This evaluates every ongoing
admitted RAW KRK history in the stated band, for either strong colour.
It does not settle KRK at every clock, orientation and history.

Assume weak turn, W=(2,0), and halfmove clock h>=95. Keep the actual
incoming trace H, the position flags and its normalized repetition keys.
The strong side wins exactly in either of the following two disjoint
families. On the complement, both players have RAW holding policies.

## Last-reply family: exact distance two

`LastReply(S,R,W)` holds, h<99, the root has fewer than three occurrences,
and H contains fewer than two occurrences of the position after the
forced weak move W->(S.x,0). These conditions evaluate current and intended
claims; the checked last-reply formula includes rook safety.

## Opposition family: exact distance four

S=(2,2), R.y>=3, h<97, and the root has fewer than three occurrences.
For each available weak reply, require the following tests. Every count
uses H, before any of these moves is appended.

* The west reply W->(1,0) is available iff R.x!=1. Require fewer than two
  occurrences of its resulting position and at least one of:
  * A rook move R->(0,y), y>=2, on its clear file/rank ray, followed by
    W:(1,0)->(2,0). Both later keys have fewer than two occurrences.
  * R.x=2 and S:(2,2)->(1,2), followed by W:(1,0)->(0,0).
    Both later keys have fewer than two occurrences.
* The east reply W->(3,0) is available iff R.x!=3. Require fewer than two
  occurrences of its resulting position and a rook move R->(4,y), y>=2,
  followed by W:(3,0)->(2,0). Both later keys have fewer than two
  occurrences.

For either rook interval, a source already on the destination file can
choose any allowed rank different from its source rank. Otherwise the
sole possible crossing rank is the source rank. The attacker can make
different choices after west and east replies. Each key is computed by
actual `play`, with the original flags preserved.

## Why this is necessary and sufficient

The checked deadline and weak five-to-four reduction imply that any win
in this clock band lies in the complete four-ply board region at W=(2,0).
An ongoing root excludes its terminal-mate disjunct. The remaining board
families are exactly LastReply and the opposition family above.

For opposition, all actual legal weak moves are the guarded west/east
moves. Each child is evaluated by a complete strong three-ply outcome
criterion. The west child needs both its rook interval and extra king
entry; the east child has only the rook interval. The first weak append
adds nothing to either later barrier query: the first queried key has
the opposite turn, while the second has a different weak king square.
Thus both children are evaluated in H itself. Necessity also checks every
current/intended root claim. Sufficiency constructs a uniform four-ply
rule-game certificate, proving child admission and ongoing status rather
than assuming them.

The last-reply family cannot win within one ply. Opposition cannot win
within three, by the checked weak-three equivalence and exclusion of
LastReply in direct opposition. Hence the displayed distances are exact.
The full RAW win/hold duality and universal strong holding policy give
the stated draw classification outside the winning region.

## Formal correspondence and limits

* `KRKSecondOppositionPrefix.lean`: original-history key transport,
  including `west_alternatives_append_iff`.
* `KRKSecondWestHistory.lean`: west-branch necessity and certificate.
* `KRKSecondOppositionHistory.lean`: both replies, root claims, complete
  opposition win/hold criterion and exact distance four.
* `KRKSecondWeakBand.lean`: `SecondBandClear`, `high_clock_force_iff`,
  `high_clock_actual_iff`, `high_clock_hold_iff`, `high_clock_draw_iff`,
  and `high_clock_distance_cases` for the entire stated band.

The shared central opposition geometry now accepts edge files at least
two; its old central history result retains its original domain. The
shared ray-prefix proof accepts an explicit last-reply hypothesis, so the
near-corner use does not assume the middle-file formula at file one.

These are local Lean results using the repository's RAW model. The
remaining near-corner/corner history bands, reflected actual histories,
lower clocks, full FIDE correspondence and global WDL/DTZ semantics remain
open. No tablebase, engine oracle or enumerated position-value table is used.
