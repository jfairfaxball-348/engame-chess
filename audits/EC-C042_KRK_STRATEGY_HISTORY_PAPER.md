# EC-C042 — adversarial paper audit (S071)

Separate same-agent review after standalone paper, not independent external
review. No engine/tablebase/class enumeration/per-position certificates. Reviewed
actual RawHistoryLayer definitions and recurrence, stopped-history append iff,
RawOccurrences.append, currentOccurrences append, clock step bound, EC-C041
rank/progress/key theorems and EC-T0037 wall source.

- Full initial-rooted traces and admission are retained. Actual Legal is witnessed
  by real move, Boolean legality and endpoint equality; no unrooted seed, erased
  history or terminal-child pruning. Parent ongoing gives child admission only.
- H queries the whole OLD history at each NEW lower winning key, explicitly
  including root/initial. It is static, sufficient and potentially restrictive.
  Losing inputs with rank-default0 are excluded by the ForceMate premise.
- Appended child can have old count1, becoming2: safe, not artificially unique.
  An incoming count2 would fail H and is not asserted a win or a draw. Future
  lower-rank queries differ from the appended child's key, so add0 by the exact
  count law. No clock reset truncates counts.
- Budget induction uses rank(parent)≤N, strict child descent and clock-free
  monotonicity to pad to N−1. It does not assume every arbitrary MateWithin
  witness already supplies the chosen minimal-rank child at its own budget.
- N0/early named mate are terminal before ongoing/claim guards. Positive-budget
  nonmate has nonempty moves, nondeadness, clock<150 and count<5. Current100/3
  and EVERY defensive intended child100/3 are excluded. Threshold endpoints,
  mate precedence and arbitrary flags remain the existing raw model's semantics.
- Essential asymmetry: strong rule branch ignores optional claims and bounds only
  its chosen descending child. Audit rejects requiring every strong legal child
  to be winning/rank-lower. Weak branch retains EVERY actual legal intended and
  executed move, and explicit nonemptiness. Captures to dead KK contradict the
  winning premise, not the Legal relation.
- Rank-six wall gives84, so clock≤15 suffices for the strict clock bound. General
  508 cannot be substituted. Both colours/all flags; conditional history family,
  no compatibility witness/nonemptiness assertion for the family or full FIDE
  correspondence. No complete outcome/holding/distance claim or certificate-
  failure draw inference.
- Four-part helper admission serves this exact KRK trace-lifting step; the append
  helper returns immediately to the main argument. No generic monotonicity detour.

Verdict: exact same-budget strategy/history lifting and partial84-ply RAW KRK
wall family close on paper. EC-C042 LOCAL_VERIFIED; formal verification and
freeze pending. All external FIDE/complete-class limitations remain explicit.
