# EC-C039 — Conditional raw lifting fidelity audit

S066, same-agent review, not independent external audit. Standalone paper and
separate adversarial audit completed before Lean. New Prepend and BudgetLifting
modules, no frozen source edits. Exact helper retains actual states and step;
main theorem quantifies every admitted s/colour/n, strict clock+n<100 and EVERY
raw prefix through n with count<3, giving SAME-budget raw RuleMateWithin from
clock-free MateWithin. No hypothesis weakened to a root count or erased path.

Helper inducts on actual Extends and prepends the same step. Main inducts on n:
zero/early mate directly Goal; otherwise clock-free nondeadness/legal-move
existence and root bounds give ongoing. Depth1 actual intended-child bounds
exclude ALL current/intended raw thresholds. Exact prepend and append clock
bound descend safety to EVERY actual child. Strong chosen move retains actual
m/hm and admitted append; weak nonempty replies and ALL admitted steps retained,
with raw soundness supplying clock-free continuation. No child-ongoing test.
No finite-tree extraction assumed: recursive witnesses used directly.

One retained initial authoring failure in Prepend: Lean's induction hypothesis
was generalised over the leading step proof, so it required `ih step` rather than
`ih`. Supplied that argument; statement/model unchanged. Logs/commands/exits/UTC
retained as authoring-failure-01. Working build/complete runner then passed.
No fresh build attempted yet; Gate F pending.

Strong sufficient all-raw-prefix certificate, not necessity, certificate existence
on any particular KRK history, numerical bound, rule-aware outcome/distance or
full FIDE correspondence. Both colours/promotions/raw flags,99/100,2/3,zeroing,
actual intended/new-key counts and adverse terminal children checked symbolically.
No full-game run/enumeration/oracle/per-position certificates/novelty.
