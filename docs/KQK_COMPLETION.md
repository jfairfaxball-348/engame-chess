# KQK — status

**Complete under the fresh WDL50 target.** The proof is frozen as
[EC-T0050](../theorems/frozen/EC-T0050/v1.md), with verified source
`c72365a8ba46f59114a2a77d9d38993f6a52df80`.
The clean 501-job Lean build and 170-declaration axiom audit passed.

## Result

For every locally legal fresh K+Q versus K position, either colour and
turn, the queen side has:

- **Strong side to move: a forced win.** Mate within 97 plies.
- **Weak side to move: a forced win** exactly when already mated, or when
  the queen is safe and a legal reply exists. Mate within 98 plies.
- **Otherwise a draw:** stalemate or an exposed queen legally captured
  into dead KK. Both sides have proved actual holding policies.

A safe queen is distant from the weak king (`dInf >= 2`) or protected by
its own king (`dInf = 1`). Dead/live is proved separately: a position is
dead exactly when the weak side is to move, it is not mated, and every
legal reply captures the queen. A drawn position can still be live.

The domain has clock zero, no prior history, no castling rights or
en-passant target, distinct pieces, separated kings, and the side which
just moved not in check. An initial-position reachability trace is not
required. The fresh game retains future draw claims; the winning strategy
avoids repetitions and finishes before the 50-move limit. There are no
fresh cursed wins or blessed losses.

The principal theorem is `EndgameChess.Rules.KQK.fresh_wdl50`, with
independent actual winning and holding policies. See the
[complete proof](../proofs/KQK_FRESH_WDL50.md) and
[geometric strategy](../proofs/KQK_STRATEGY.md).

## Scope boundary

Exact distances such as **M4/Mn are optional and are not a completion
gate**, just as the unfinished longer-distance KRK catalogue is out of
scope. Incoming clocks/histories, castling positions and a broader FIDE
correspondence are not claimed. No tablebase or position enumeration is
used as a proof oracle. KPK is selected next; its [plan](KPK_PLAN.md) is
installed but unexecuted.
