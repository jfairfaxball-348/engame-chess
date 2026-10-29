# KRK — status

**Complete under the [outcome target](CHARTER.md#parity-target-hard-boundary-owner-2026-10-29)**
(owner, 2026-10-29). Every legal KRK position has a proved result with perfect
play, either colour, either side to move. The proofs are frozen; see the
[ledger](../theorems/LEDGER.csv).

## The result
With the strong side having king and rook:
- **Strong side to move: always a forced win.** `krk_strong_arrival_force` (EC-T0019).
- **Weak side to move:** forced win if the weak king is already mated, or the rook is
  safe (distant or protected) and the weak side has a legal move. Otherwise it is a draw
  (the rook falls, giving dead KK, or stalemate). `krk_weak_force_safe_iff`, with dead/live
  in EC-T0007.
- **Within the 50-move rule** from a fresh clock: mate within 97 plies (strong to move)
  or 98 plies (weak to move), so every win above is a real win under the 50-move rule.
  `KRKCentral.fresh_outcome`, `fresh_arrival97`, `fresh_weak98` (EC-T0048).

## Optional, not a gate
- **Exact distance to mate.** Exact for mates within 13/14 plies (EC-T0049), with
  the 97/98-ply upper bound elsewhere. Continuing past 14 plies is optional.
- **Beyond the target, kept as frozen evidence**: RAW history-aware clock bands,
  incoming repetition, claims, castling exclusions
  ([archived note](../research/KRK_POSITIVE_CLOCK_FRONTIER.md)).

## For KQK
The wall/box forcing lemmas (`KRKForcing`, `KRKBox`, `KRKCentral`) are the
parts most likely to transfer. KQK starts only when the owner selects it.
