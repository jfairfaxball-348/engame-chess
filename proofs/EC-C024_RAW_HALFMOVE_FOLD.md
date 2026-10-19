# EC-C024 — Raw legal-trace halfmove fold

S036. Classical counter construction, no novelty claim. Sources: FIDE Laws
(effective 2023-01-01), Articles 9.3.1–2 and 9.6.2, retrieved this session;
source/hash and actual clause extracts in sessions/evidence/S036/. The 75-move
clause explicitly preserves last-move mate precedence; no adjudicator is built
here. Also use the owner-reviewed kernel Move/isLegal/play and S035's unchanged
five RawTrace modules, anchored at 526a298b80ef04541e518a3dcc62f861c8f51c5c.
No tablebase, engine, enumeration or stored result is a proof source.

## Exact definitions and domain

At source q and full Move m, Pawn(q,m) means q.board m.src is exactly
some (q.turn,pawn). Zero(q,m) is the Boolean Pawn test OR occupied destination.
OrdinaryCapture(q,m) means the destination holds a piece of colour different
from q.turn. EPCapture(q,m) means Pawn, ep=some dst, different source/destination
files, empty destination, and an opposing pawn at (dst.file,src.rank).
CaptureEvent is OrdinaryCapture OR EPCapture. This is the kernel's capture
EVENT specification, not a material-count-decrease definition. No global
material-count equivalence is asserted; the event's connection to FIDE remains
the existing human-reviewed kernel encoding, not a formal theorem about English.

For EVERY legal m, Zero=true iff Pawn OR CaptureEvent. Proof: legal implies
isPseudo, hence targetOK. An occupied destination therefore contains an enemy
nonking. If Zero holds, its pawn branch gives Pawn; otherwise the occupied
destination gives OrdinaryCapture. Conversely Pawn sets Zero; an ordinary
capture supplies occupancy; an ep capture supplies Pawn even with empty dst.
The kernel's only extra capture-removal branch in play is epCapture, which is
guarded by Pawn. Nonpawn moves cannot use it. In particular a legal nonpawn
move with empty destination cannot capture; castling only relocates one's rook.
No assumption about a friendly occupied destination is made outside legality.

## Main facts and proofs

1. Event cases (all q,m): a source pawn resets for EVERY promotion choice,
destination, and flags; every occupied destination resets (only interpreted as
capture on legal moves); a source nonpawn and empty destination do not reset.
Proof by Boolean evaluation and rewriting source/destination equalities.
These cover pawn singles/doubles, promotion and en passant with empty dst.
2. For every q,m, canCastle q m=true implies empty destination. Its two branches
force dst=(g,home) or (c,home), respectively, and explicitly require that square
empty. Together with the source king, case 1 proves castling does not reset.
Similarly any quiet king/rook move with empty dst increments, even if rights
are lost or the ep flag changes; neither flag occurs in Zero.
3. Legal event equivalence is the universal proof above. It uses targetOK,
not a case-by-case game prefix or an unproved material count invariant.
4. Define clock on the existing stored Trace: clock(start)=0;
clock(snoc prior m hm)=if Zero(q,m) then 0 else clock(prior)+1.
For EVERY raw state s, Move m, and hm:isLegal(erase s)m=true, clock of append's
trace equals precisely that conditional expression. Unfold append and the fold.
Root and actual trace prefixes are unchanged; the counter is derived data.
5. For EVERY t:Trace q, clock(t) <= t.moves.length. Structural induction:
root 0<=0. At snoc, Zero gives 0<=length+1. Otherwise the induction hypothesis
clock(prior)<=length(prior) implies clock(prior)+1<=length(prior)+1, exactly
the appended move count. No class enumeration or arbitrary seed clock.
6. For EVERY actual append, clock(child)<=clock(parent)+1: reset branch is
nonnegative; increment branch equality. All lengths/counters measure BOARD
PLIES. Fifty moves by each player is 100 plies; seventy-five is 150.

## Adversarial controls and boundaries

Empty root gives zero. Quiet nonpawn increments, ordinary capture resets,
pawn single/double and promotion reset, ep resets despite empty dst. Castling
and quiet king/rook loss of rights increment; resetting on lost rights would
be wrong. These are universal symbolic case arguments, not claims of executed
sample games. No compatible initial-rooted promotion/ep/castling prefix is
constructed or asserted. Exact S035 append_spec retains the full move/position
prefix and increases move count by one even on reset; nothing is truncated.
No terminal filter is added, so the fold remains defined past a future raw
150-ply threshold or earlier draw whenever kernel legality permits a move.

The claims concern RAW traces only. No no-earlier-terminal admissibility,
repetition key, current/intended claims, automatic terminal rules, mate priority
classifier, complete HistoryLayer instance, holding/outcome theorem, sufficient
budget lifting, uniform KRK numerical bound, DTM/DTZ/WDL, Syzygy parity or
initial-position result follows. In particular clock<=total length never
proves a remaining budget below 100. EC-C023 and EC-C024 Gate Z stay separate.
