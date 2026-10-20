# EC-C040 — adversarial paper audit (S067)

2026-10-20. Separate same-agent review after writing the standalone argument;
not independent external review. Reviewed S029/S030 paper and exact frozen
LowerPursuit, WallForce, RankAdvanceRescue, StrategyTransport, AxisWalls,
ClearEntry, OffRankSetup, SameRankSetup and SafeSetup source. No Lean build,
engine, tablebase, class enumeration or stored position diagnostic was run.

- Quantifiers: both colours, exact KRK, strong turn, no weak check. Legal arrival
  implies that premise; no arbitrary illegal-check input is claimed. Flags remain
  arbitrary at the target; source noRights is explicit for every transport.
- Transport: the frozen theorem returns only ForceMate. Audit rejected treating
  that as equal-budget evidence. The new induction in paper §1 preserves the
  SAME N using ordinary source choices, target weak completeness and explicit
  nonemptiness. This must be newly formalised; flags need not map as records.
- Branch budgets: rejected summing finite reply bounds. Every weak node is given
  a common numerical successor bound and costs one, retaining ALL legal replies.
  Nondeadness follows from a winning child; it is not an extra assumption.
- Pursuit: initial offset one can add one tempo before the wide-case two tempos
  and king step. Thus eight, not six plies is the conservative recursion cost.
  Aligned/upward exits can occur after any pair and cost no more. m=0 has no
  strict-sign inputs; m=1 cannot recurse to a valid m=0 input. Both physical
  directions use the frozen geometric action statements, not unproved symmetry.
- Wall: normalization adds two at EVERY gap level, not merely once globally.
  A(n,g)=U(n−1)+62+4(g−1) pays that cost plus each king-rank step. g≤6 gives
  A≤U(n−1)+82≤84n. The rank-advance rescue pays four, not two, and accepts a
  threatened rook only on a strong turn. All return walls permit that threat.
- Boundary n=1: upper-band and nonmating aligned exits cannot exist; the aligned
  check is actual edge mate in one. U(0) is never used to claim a nonexistent
  rank-seven strict wall. No unsigned subtraction is used outside n,g≥1.
- Setup: off-rank retreat may reduce the original vertical gap to one. The
  perpendicular entry branch remains necessary and paid. Same-rank back-rank
  setup can use preparation AND protected entry; four plies covers both. All
  canonical changes are logical transport, not chess moves. The weakest terminal
  branches use named mate; explicit reply witnesses prevent stalemate claims.
- Captures: each weak node uses safety/reply completeness. No legal rook capture
  to KK is discarded. A hanging strong-turn rook is repaired before giving the
  defender another turn. Unchosen strong moves are outside the strategy.
- History: a finite decreasing macro measure does not automatically give unique
  normalized keys. Incoming history is distinct from generated repetitions.
  508 is too large to instantiate clock+n<100 at any nonnegative clock. No rule
  win, holding classification, optimal distance, DTZ or class closure is inferred.

Verdict: the stated coarse clock-free bound closes on paper with the quantified
frozen action facts and the new same-budget induction. EC-C040 LOCAL_VERIFIED;
formal proof and freeze pending. No theorem count or rule-aware coverage change.
