# EC-C045 — Universal admitted RAW KRK clock-bounded termination

S076,2026-10-20. Classical material closure and decreasing-counter argument,
no novelty claim. Sources: actual FIDE2023 legal-move kernel/play/castling,
frozen KRK material/weak replies, raw clock fold and stopped-history Layer.
Standalone paper/separate same-agent audit BEFORE Lean. No engine/tablebase,
class enumeration or stored position certificate. Frozen source remains unchanged.

## Exact domain and claim

Fix either strong colour σ. Positions are actual RawHistoryLayer.State values,
retaining an initial-rooted legal trace and its strict-prefix admissibility proof
under the EXISTING raw classifier. Both turns and ALL kernel flags are allowed.
No winning-strategy, rook safety, low clock, repetition histogram or noRights
premise is imposed. Every actual legal board move is retained, including bad or
unchosen strong moves. This theorem does not quantify raw moves after a terminal
as if they were admitted play.

Let Regionσ(s) mean exact KRK of colour σ at the endpoint (some distinct S,R,W),
OR not Ongoing(s). Let

    P(s)=if Ongoing(s) then150−clock(s.trace) else0.

An admitted path is a finite sequence of existing BoardStep edges BETWEEN typed
admitted states. A length-zero path retains the exact state; a successor prepends
one actual stored legal append. Each child is admitted, even when terminal.
No terminal-child or defensive-outcome filter is added.

For EVERY typed BoardStep s→t with Regionσ(s), prove Regionσ(t) and
P(t)+1≤P(s). Hence EVERY admitted length-n path from such s to t satisfies
Regionσ(t) and P(t)+n≤P(s). In particular from ANY admitted exact KRK root of
clock h, every board play has at most150−h plies if the root is ongoing, and
ZERO if already terminal. Terminal includes mate/dead/stalemate/automatic draw
under the chosen raw classifier; this is not a statement that every terminal is
a draw. A maximal board path ends not ongoing, and some terminal continuation
exists within that bound. Arbitrarily truncated prefixes need not be terminal.

This is a universal RAW termination theorem, NOT complete outcome/holding/FIDE
correspondence or exact distance. Successful claims are separate zero-board-ply
stopping actions and can only end play earlier. Failing a sufficient winning
certificate is still not a draw proof.

## Direct dependency admission

The blocked KRK outcome/holding step needs a finite all-branch history horizon,
not just the selected 442-ply strategy or a sufficient incoming-count family.
Frozen krk_strong_reply assumes noRights; raw clock≤old+1 alone does not prove
strict increase in ongoing KRK. The smallest missing statements are all-flag
strong material/quiet closure and the exact KRK-or-dead-KK one-step law. They
immediately feed this actual admitted path potential. Exit: return directly to
all-history holding/outcomes/claims and full FIDE bridges, not an unrelated
generic material/count lemma series. Strong castling must not be excluded.

## 1. Legal targets and the castling material branch

Exact KRK has only strong king/rook and weak king, so there is NO pawn at any
source square. A legal mover must be its turn's own piece. targetOK forbids an
own piece and ANY king as a destination. Therefore an occupied legal target can
only be the strong rook, and then the mover is the weak side. On a strong turn
EVERY legal destination is empty, so the frozen raw zeroing definition is false:
source is nonpawn and destination empty. Arbitrary raw ep cannot remove a piece
because play's epCapture branch requires an actual pawn source.

A strong ordinary king move is a one-square step, with no promotion, and the
frozen play_board_simple identity moves only that king. Empty destination
ensures it differs from both old own pieces and weak king; exact new KRK follows.
A strong rook move likewise has no promotion, and its play_board_simple identity
moves only the rook to an empty square. No far-king-distance or ordinary StepM
representation is needed for MATERIAL closure; actual legality already supplies
the move and any mover safety used elsewhere.

For a strong KING CASTLE, derive the actual branch from isPseudo's kingGeom OR
canCastle. NoRights is NOT assumed. canCastle fixes old king at(e,home rank),
new king at(g or c,home rank), and the required own rook at(h or a,home rank).
There is only one own rook, so this identifies its old square. canCastle forces
both the king destination and crossed rook destination(f or d) EMPTY. Thus the
weak king occupies none of those new squares, and exact old material also
excludes it from the two removed squares. The king/rook destinations are distinct
by their files. Evaluate the actual play formula: remove the old king and old
rook, place king at g/c and rook at f/d, keep the weak king unchanged, add nothing
else. This proves exact KRK at the actual endpoint. Rights/ep are updated by play
and retained in the full state; their values are not erased from future moves.

Only the two CASTLING SCHEMAS are split; coordinates of the weak king remain
universally quantified. This is symbolic rule analysis, not board enumeration
or a list of position certificates. Clock quietness already follows from the
actual nonpawn/empty target, including this two-piece move.

## 2. Weak moves and retained-material quietness

Frozen lone_move_cases covers EVERY legal weak move with arbitrary flags: either
exact KRK survives with the SAME strong king/rook squares and a moved weak king,
or the rook is captured giving KK. Weak castling is impossible because there is
no weak own rook, as that theorem already proves; raw rights cannot create one.

In the surviving-KRK branch, the actual source is a weak king, hence nonpawn.
If its legal target were occupied, the target argument above identifies it with
the old strong rook square. At the played move's destination, play places that
source weak king (a nonpawn remains a king regardless of a raw promotion field;
actual legality in fact requires none). But the surviving-KRK certificate still
places the strong ROOK on that SAME old square. Contradiction in piece kind.
Therefore the destination is empty and the move is nonzeroing. This argument
retains the actual move and the NEW endpoint; it does not count pieces via an
unproved material oracle or assume the desired quiet-clock conclusion.

In the KK branch, the frozen legal-into-KK theorem makes the actual child dead,
for any flags and either orientation. A dead endpoint cannot be raw ongoing by
the frozen ongoing iff. Its capture may reset the clock to0, but it is terminal
and no later admitted board move can follow. No legal capture is pruned.

Together: EVERY legal actual KRK move either yields exact KRK with zeroing=false,
or a dead KK child. This is all-move closure, not safety of arbitrary strong
moves or the chosen rank policy. A bad strong move may yield DEAD KRK; that is
still quiet retained material and terminal, and remains in the quantifiers.

## 3. Typed append guard and exact child clock

Existing BoardStep s t is an actual m, legality and equality t.val=append s.val m hm.
Since t is admitted, the frozen stopped-history append equivalence gives that
s is admitted AND its current raw classifier is ongoing. Thus ANY typed step
forces parent Ongoing; there is no typed step from a terminal state even if raw
Legal still offers moves on its erasure. At an ongoing parent, full reply lifting
still admits EVERY legal child, including terminal children. No ending reply has
been deleted to make a forcing statement easier.

For a retained quiet KRK move, frozen append_clock at the ACTUAL stored append
reduces to clock(t.trace)=clock(s.trace)+1. Incoming history is not reset or
truncated; this only updates its derived halfmove counter. Repetition can stop
a child earlier and does not weaken the bound. A zeroing rook capture is the
dead-KK terminal branch from §2, never an ongoing clock-reset loophole.

## 4. Region and strictly decreasing potential

Take a typed step from Regionσ(s). The terminal-parent disjunct contradicts its
forced Ongoing guard, so parent material is exact KRK. Ongoing iff gives
clock(s)<150. Apply the one-step law:

- Retained KRK gives Regionσ(t). If t is ongoing, its exact clock increment
  implies (150−clock(t))+1≤150−clock(s), using clock(s)<150. If t is terminal,
  P(t)=0 and1≤150−clock(s) gives the same inequality.
- Dead KK is not ongoing, so Regionσ(t) and P(t)=0. Even if capture reset its
  counter, parent clock<150 still gives P(t)+1≤P(s).

The potential does NOT classify a clock150 mate as a draw: mate-first status is
terminal either way and has potential0. Root mate/automatic draw/dead/stalemate
also have potential0. A root clock≥150 cannot be ongoing under the classifier;
no negative or silently truncated active budget is used.

## 5. Universal path bound, maximal endpoint and existence

Induct on typed path length. Zero is exact-state equality. A head step gives
child Region and P(child)+1≤P(root); induction on the remaining actual typed
path gives P(endpoint)+n≤P(child). Add inequalities to get
P(endpoint)+(n+1)≤P(root). This proves the universal bound on EVERY finite prefix,
not merely on one cooperative or winning continuation. An infinite admitted
board play is impossible because its arbitrarily long prefixes violate this
fixed natural bound.

At ANY admitted ongoing state, ongoing iff supplies a legal move and frozen
full reply lifting supplies an admitted BoardStep. At any not-ongoing state,
§3 excludes such a step. Thus no admitted successor iff not ongoing. In
particular a MAXIMAL finite path ends terminal; this does not say an arbitrary
short prefix is already mated or drawn.

For existence of a terminal continuation, induct well-foundedly on P(s) in the
Region. If not ongoing, choose zero path to itself. Otherwise select any legal
move/witness, keep its admitted child, and use its strict smaller potential to
continue. Prepend the actual step and add one to the bound. No outcome oracle,
optimal strategy or finite class enumeration is used. The universal path theorem
ensures all choices also respect the same cap.

## Status and remaining work

LOCAL_VERIFIED after separate same-agent audit; Lean/Gate F and separate Gate Z
pending.41 frozen bundles unchanged. Actual chosen RAW model only; all flags,
both turns/colours and all legal moves covered, including castling and terminal
reset. Complete all-history holding/outcome classification still needs genuine
claim/terminal strategies and full FIDE correspondence; exact WDL/DTZ semantics
and distances remain separate. No class-completion percentage or novelty claim.
