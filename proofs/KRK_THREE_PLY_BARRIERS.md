# Three-ply KRK regions and two incoming-key barriers

This is a checked working extension of the [last-reply
classification](KRK_LAST_REPLY.md). It evaluates the complete strong-turn RAW
outcome for ongoing admitted histories with halfmove clock h≥96. KRK as a
whole remains open, including lower-clock history barriers and full FIDE
correspondence.

Write S,R,W for the strong king, rook, and weak king. Use the coordinate
predicate LastReply from the four-row edge table and its transpose, including
rook safety. Let M(S,R,W) be the already checked immediate-mate formula.

## The complete board region

Define two sets of coordinate witnesses:

* King entries are squares T with d∞(S,T)=1, T≠R, d∞(T,W)≥2, and
  LastReply(T,R,W).
* Rook entries are squares T≠S,W on a clear rook line from R, with
  LastReply(S,T,W).

Then a legal strong arrival can force mate within three board plies exactly
when M holds or either entry set is nonempty. These definitions contain only
coordinates, clear segments, and the explicit edge table. They contain no
recursive outcome predicate. The table restricts king entries to its named
edge-offset slots. Rook entries are rank/file intervals or crossings with
those slots, rather than arbitrary future game trees.

The converse covers every actual legal strong move. A mating move is included
in M. Every other winning first move must reach the complete last-reply region
by the two-ply theorem. An ordinary move relocates either S or R and therefore
gives one of the displayed coordinate witnesses. Actual castling puts the
king/rook on files (6,5) or (2,3) of their home rank. Neither resulting pair
can satisfy any row of LastReply in either orientation. Castling is therefore
excluded by geometry, without deleting castling rights or legal alternatives.

## History barriers are two explicit key counts

Fix the entire original incoming trace H, including the current root q. For a
candidate ordinary entry move m, write q1=play(q,m). The last-reply table
determines exactly one actual legal weak move w=(W,U,none), not merely a board
up to symmetry. Write q2=play(q1,w). Let c_H(a) count the normalized RAW key
of a in H. An entry is clear exactly when

    h < 98,    c_H(q1) < 2,    c_H(q2) < 2.

The complete high-clock criterion is

    strong actual win
      iff immediate mate
          or a king entry with a clear pair of keys
          or a rook entry with a clear pair of keys.

The canonical first move and forced reply are checked with the actual kernel
legality predicate, preserving flags and all path restrictions. The quantified
witnesses are landing coordinates in the explicit region, not unknown WDL
values or strategy trees.

Why the two counts suffice: q1 has one new occurrence, hence its current count
is c_H(q1)+1. Its only intended child is q2. The q1 append cannot change the
count queried at q2 because their turns differ, so their normalized keys
differ. Thus no current/intended repetition claim exists exactly when both
old counts are below two. Strong KRK moves are nonzeroing; the weak root q1
has clock h+1. Its absence of an intended clock claim is h+1<99, equivalently
h<98. These facts also keep the intermediate states below automatic thresholds.
The original trace is never reset or pruned.

For h≥96, a winning nonterminal first child has h1≥97. The complete weak-turn
classification therefore applies and proves necessity of the entry test
against every legal first move. Conversely a clear entry gives an actual
three-ply certificate on that same history. At h≥98 entries are excluded by
the clock inequality, recovering the immediate-mate-only result.

## Outcomes and distances

The RAW certificate/policy bridge gives the actual-win equivalence. Its dual
gives a defender holding policy precisely when the criterion fails. Every
winning high-clock strong root has distance at most three. If M fails, a
certificate of distance at most two is impossible: turn alternation reduces
strong two-ply mate to immediate mate. Thus the winning distance is one or
three. These are board-ply distances in the current RAW model, not a claim of
global DTZ/FIDE parity.

## Lean correspondence

`KRKLastReplyKey.lean` proves uniqueness of the actual weak move, the
two-query claim test at a weak root, and its high-clock actual-win instance.

`KRKThreePly.lean` defines KingEntry, RookEntry and Three, proves actual
castling cannot enter LastReply, classifies every actual entry move, and proves
`strong_three_iff`.

`KRKThreePlyHistory.lean` defines EntryClear and ThreeHistory, proves
`entry_no_claim_iff`, constructs a three-ply certificate from every clear entry,
and proves `high_clock_force_iff`, `high_clock_actual_iff`,
`high_clock_hold_iff` and `high_clock_exact_three`.

The focused build `lake build EndgameChess.Rules.KRKThreePlyHistory` passed.
The aggregate `lake build` passed (257 jobs), and `lake env lean AxiomCheck.lean`
passed with only `propext`, `Classical.choice`, and `Quot.sound` for the new
public declarations.
