# EC-C048 — separate adversarial paper audit

Same-agent audit after standalone paper, before any C048 Lean. No independent
external review. Existing raw layer, full rule recurrence, actual policy/path,
terminal inversion and all-move KRK fuel reviewed. No tablebase/engine/enumeration.

* Positive certificates cannot be silently called actual policies. Proposed
  ActualWin is independent: global legality, full-prefix terminal/claim safety
  and explicit UNIFORM board-ply cap. The cap cannot be omitted; choosing merely
  an F-child can cycle on an unrestricted graph. Forward uses concrete Region
  fuel and does not assert a decreasing certificate rank outside that Region.
* At own ongoing nodes F selects Some actual winning child and declines any
  optional claim. On opponent ongoing nodes NO current/intended claim and ALL
  actual children are retained. Correct claims stop at zero plies, so absence
  must be proved at parent, not after execution. Off-winning own choices remain
  globally legal, preventing a partial strategy on off-branch histories.
* Safety covers zero prefix. Terminal draw/opposite mate cannot satisfy it.
  Goal roots use horizon0. Terminal mate at150 remains named mate; fuel0 alone
  does not give Goal. Nonempty actual ongoing replies exclude vacuous stalemate.
* Forward full-prefix F-invariant alone is labelled WinningSafety, not complete
  winning. Only after adding the Region's universal finite horizon does it
  satisfy ActualWin. This avoids a hidden infinite-play victory convention.
* Converse extracts the SAME B budget from ANY legal bounded winning policy,
  by induction on B and prefixing its actual compliant edge. Uniform parent
  bound gives every child horizon B-1, not merely individual existential bounds.
  Opponent branch retains all children and noClaim; own branch takes the actual
  selected Some move. At B0 any ongoing successor contradicts the path bound.
  No finite-board maximum or class enumeration is used.
* Maximal board endpoints under WinningSafety cannot be an ongoing own claim;
  frozen policy-maximal/stopped theorem then gives actual raw terminal, and
  safety makes it named Goal. Stopped continuation existence within fuel cannot
  stop at an own claim either. Opponent claims are explicitly absent. Arbitrary
  truncated prefixes need not already mate; complete plays stop by the cap.
* Both named-player/material colours, turns/all actual flags/incoming histories
  remain. No assumed compatible independent count vector replaces State. The
  iff on terminal Region states is safe: arbitrary terminal non-goal has neither
  F nor ActualWin, while terminal goal has both. Generic converse needs no KRK.
* This is a strategy semantics bridge, not an evaluated geometric outcome
  formula. Low-clock arbitrary history geometry, full FIDE correspondence and
  exact global WDL/DTZ remain open. Do not mark KRK closed from this theorem.

Verdict: exact strategy soundness/completeness on Region and same-B general
converse close on paper. Formal verification and separate freeze still required.
