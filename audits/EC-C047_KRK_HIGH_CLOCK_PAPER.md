# EC-C047 — separate adversarial paper audit

Prepared after the standalone C047 paper, before new Lean. Same-agent audit,
not independent external review. Actual existing admitted history/layer,
claim thresholds, mate recurrence, KRK material closure and previous king-check
lemmas inspected. No board enumeration or tablebase/engine consultation.

* Initial-rooted provenance is essential to strong no-mate-at-root. An arbitrary
  malformed KRK board could have adjacent kings. Paper uses actual last Legal
  predecessor, initial_not_KRK and legal_mover_safe; it does not simply assume
  kings apart or mistake arbitrary kernel flags for reachable history flags.
* If root is strong to move, the last mover was weak, and weak safety excludes
  adjacent kings. Strong inCheck depends only on lone-king adjacency. The proof
  uses symmetry of distance and actual KRK check identities. If root is weak to
  move, weak named Goal fails its turn guard independently of root check.
* KRK-or-dead is a separate preserved invariant. Region=KRK-or-terminal alone
  would admit an arbitrary terminal weak mate and cannot prove strong holding.
  A dead parent has no typed successor; retained KRK and terminal dead KK
  children remain. This distinction prevents a false all-terminal-no-weak-goal
  claim on arbitrary terminal states outside material.
* Strong holding selects a GLOBALLY LEGAL policy and proves all-prefix safety;
  no assumption of weak nonforcing is used circularly. Then holding's converse
  excludes weak forcing. Additional claims can stop draws but never weak mate.
* Weak h>=99: no blanket quiet-move assertion. A hypothetical strong certificate
  covers some nonempty actual child. Dead-capture branch contradicts projection
  to clock-free forcing at a dead endpoint. Only under that certificate does
  quietness follow, giving actual prospective h+1>=100. AvailableThreshold
  includes intended claim even when current h=99/current count<3.
* Actual full trace at child is retained by typed BoardStep append equality.
  The intended claim is at the PARENT before executing its announced move,
  not a new claim turn after playing it. No side-to-move claimant reversal.
* Strong h>=98: quiet certified child is weak turn h>=99. Terminal child must
  already be named Goal; ongoing child cannot force by the weak theorem.
  Immediate mate is sufficient even at clock150. Correct own claims may be
  declined, so h>=100 on the strong root does not by itself imply draw.
* Root Ongoing is mandatory in high-clock statements. At h>=150 a nonmate root
  already draws; actual root mate is terminal win and excluded from ongoing
  rather than mislabelled. Weak turn terminal mate is also excluded correctly.
* No numerical classical mating maximum or low-clock repetition criterion is
  inferred. Every incoming key count/trace and legal reply remains. Both-hold
  follows from actual policies on each side, not a failed sufficient certificate.
  Full FIDE correspondence, optimal global distances and WDL/DTZ stay open.

Verdict: exact all-history strong nonloss and ongoing high-clock forcing
criteria close on paper. Local one-ply optimality is an immediate corollary:
on a winning strong h>=98 root, W(1) holds and W(0) fails by ongoing nonmate.
No broader exact-distance or class-closure claim follows. Gate F/Z remain.
