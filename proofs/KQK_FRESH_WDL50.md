# Complete fresh KQK WDL50

This is a classical endgame re-proof over the repository's legal-move
kernel, not a novelty claim. It uses general geometry and induction;
no tablebase, engine, stored position table or computed retrograde proof
is used. Exact mate distances are outside the result.

## Exact domain and outcome

Let `σ` be the queen side, with distinct strong king `K`, queen `Q` and
weak king `W`. `KQK.IsKQK` asserts this exact board. `KQK.FreshLegal`
requires no castling rights, no en-passant target, separated kings
`2 <= dInf K W`, and that the side which just moved is not in check.
These are local conditions; no trace from the standard initial position
is required. Start with clock zero and an empty past.

\[
 \operatorname{Safe}(K,Q,W)\iff d_\infty(Q,W)\ge2
                    \ \lor\ d_\infty(K,Q)=1.
\]

| Turn / condition | Queen side | Side to move | Sufficient mate bound |
|---|---|---|---|
| Queen side to move | Win | Win | 97 plies |
| Weak side already mated | Win | Loss | 0 |
| Weak turn, safe queen and a legal reply exists | Win | Loss | 98 plies |
| Every other weak turn | Draw | Draw | Holding |

The principal declaration is `EndgameChess.Rules.KQK.fresh_wdl50` in
`formal/EndgameChess/Rules/KQK/FreshOutcome.lean`. It proves the queen
side has an independently defined actual bounded winning policy exactly
in the winning rows, the weak side has no actual winning policy, and
both sides have actual holding policies exactly in the drawn row.
`fresh_uniform98` proves a rule-layer bound of 98 for every winning case;
`fresh_strong97` gives 97 on the strong turn. `fresh_force_iff` equates
fresh actual winning with clock-free forcing: there are no cursed wins
or blessed losses. None of these are optimal-distance assertions.

## Confinement and cost

The [strategy source](KQK_STRATEGY.md) gives the geometric lemmas. A strict
separating rank `K_y < Q_y < W_y`, with the weak king not in check on the
strong turn, forces mate within 91 plies, on either side of the queen
file. This includes preparation of an arbitrary strong king below it.
In the prepared region maintain

\[
 K_y+1=Q_y\le5,\quad Q_x\le K_x\le W_x,\quad Q_x<W_x,\quad Q_y<W_y,
\]

and use `P = 2(7-K_x)+2(7-Q_x)+4(5-Q_y)`. A defended king-file step
decreases `P` by two. When the king is within one file behind the weak
king, a protected queen slide to `W_x-1` decreases it by at least two.
With the queen exactly one file behind, noncheck implies a rank gap of
at least two. A king crossing and protected queen-rank advance cost four
plies and decrease `P` by at least four. Every recursive weak node has
an explicit reply witness, as well as coverage of all legal replies.

Rank five and the rank-four right edge have direct repairs costing at
most 33. The prepared bound is `P+33 <= 77`. Charge preparation jointly:

\[
 2(Q_y-1-K_y+|K_x-Q_x|)+4(7-Q_x)+4(5-Q_y)+33\le91.
\]

Rank-six walls and the initially narrow rank-five corner finish
separately inside this ceiling. No pass move or favourable reply is
assumed. Captures, blockers and queen-only stalemate traps are included.

## Universal entry

Normalise a separated king pair so `K_y+2 <= W_y`, using reflection,
transposition or anti-transposition preserving diagonal and orthogonal
queen rays. For an off-rank queen, orient `W_x >= 4`. If needed, prepare
the queen on file zero or one. Choose between them so that an explicit
horizontal weak escape is not on the queen diagonal. Fixing a single far
file can stalemate when the king guards the other escapes.

Every reply to the chosen preparation leaves `W_x >= 3`, the weak king
at least one rank above the strong king, and the weak king off the queen
rank. The complete resulting region costs at most 95:

* A clear vertical slide enters a wall. Small far files retain an escape
  even on the last two ranks with only a two-file margin.
* Otherwise the kings have a file gap of at least two. With a queen/weak
  rank gap of at least two, horizontal entry works. Its narrow-corner
  obstruction has a direct mate in the standard rook-mate pattern.
* In the remaining tight geometry, advance the king one rank. All weak
  replies retain file separation at least two and stay below the queen.
  The next file wall is protected. Its narrow corner again uses a direct
  mate instead of the stalemating intended wall.

This covers both sides, blockers, board boundaries and replies reducing
the rank gap to one. Initial preparation costs at most two, yielding 97.
For a queen sharing the king's rank, use a backward king step if the rank
is positive; repair the rank-five corner with a queen check first. On
rank zero, use clear entry, an axis change, protected entry, or a one-step
king preparation aligned with the weak king to prevent descent to rank
one. All same-rank cases fit 97. `StrongEntry.strong_entry_bound` thus
covers every strong-turn locally legal board, not only legal arrivals.

## Weak turns, holding and dead/live

Every weak legal move retains KQK or captures the queen into KK. Safety
retains it for **all** replies, each a strong legal arrival with bound 97;
the weak root costs at most 98. A mated root uses the zero-ply goal.

An adjacent unprotected queen is legally captured into dead KK, an
explicit weak holding choice. A nonmated root without moves is stopped
and drawn. Material closure proves no cooperative legal continuation
can mate the strong king: KQK retains separated kings or enters dead KK.
Thus any legal policy holds for the queen side.

`fresh_dead_iff` separately proves

\[
 \operatorname{Dead}(q)\iff q.\mathrm{turn}=\overline\sigma
 \ \land\ \neg\operatorname{Mated}(q)
 \ \land\ \text{every legal reply is KK}.
\]

A noncapturing weak reply is live by the strong-turn forcing theorem.
Conversely, a nonmated root all of whose replies are dead KK is dead.
`fresh_live_draw_example` checks Ka1/Qd4 versus Kd5 on the weak turn:
capture draws, while the cooperative Ke6 continuation permits mate.

## Fresh rules and independent policies

`FreshGame.State` records the kernel board, only positions visited since
the root, and its reversible-move clock. Future legal moves update the
clock with the existing `RawClock.zeroing` pawn/capture definition and
count normalised repetition keys. The concrete rule layer retains
current/intended 50-move and threefold claims, automatic 75-move/fivefold
stops, kernel deadness and stalemate, with checkmate as the terminal goal.
It assumes no incoming histogram, initial-rooted trace or history symmetry.

`FreshGame.fresh_sub100` lifts a supplied board certificate using the
existing general decreasing strategy rank. Every chosen strong move and
**every** weak reply descends. Equal normalised keys have equal rank, so
every visited key is distinct: occurrence count is one, including at
intended successors. The clock rises by at most one per ply and resets
on actual zeroing events. With bound 98, no claim or automatic draw can
interrupt a winning line.

`FreshGame.ActualWin` is independently defined by a legal policy, correct
terminal outcomes on every compliant prefix, preserved opponent claim
options, and a uniform finite horizon. `actual_win_iff_rule` proves its
equivalence to finite rule certificates. Its least-witness rank is only
a proof measure, not a computed distance catalogue. `FreshGame.Hold`
uses legal policies preventing the opposing mate on every compliant
prefix; `hold_not_win` excludes opposing forcing.

## Fidelity and boundaries

This settles the selected fresh KQK target. Kernel legality, mate and
deadness are normative inputs, as for the existing classes. A broader
physical/FIDE correspondence is not claimed. Positive incoming clocks,
incoming histories, castling positions, exact DTM/DTZ and other material
classes are outside the result.

Escape and protection premises are essential: additional queen rays do
not monotonically preserve rook wins. The proof repairs empty-response
traps instead of inferring a win from them. General proofs use coordinate
arithmetic and induction, not board enumeration; concrete kernel `decide`
examples are supplementary controls only. Certification, source identity
and observed checks are recorded in the [ledger](../theorems/LEDGER.csv)
and its KQK manifest, not inferred from this prose.
