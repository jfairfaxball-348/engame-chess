# EC-C039 — Separate adversarial paper audit

S066, reviewed before Lean against frozen EC-T0036 and complete raw Layer sources. Same-agent,
not independent external audit. This audits the exact conditional statement.

- n=0/early mate: Goal succeeds immediately, no invented extra claim turn or ply.
  Extra safety hypotheses are sufficient, not necessary, at terminal leaves.
- Strict99/100: root+remaining budget<100 gives EVERY interior child's clock<100;
  merely checking current<100 would miss intended claims at99. Actual append clock
  bound covers reset moves; no assumption of uniform nonzeroing behaviour.
- Repetition2/3: count at EVERY actual prefix INCLUDING next intended child is
  below3. This uses the NEW child's key in its actual extended history; replacing
  it with the root key query would be unsound. No compressed/arbitrary counts.
- Every defender move remains quantified. A legal capture to dead KK would refute
  clock-free MateWithin and cannot be removed to manufacture a certificate.
- Parent ongoing follows from actual nondeadness, existence of a Legal successor
  and strict automatic150/5 bounds. No blanket ongoing assumption on children.
  The IH separately treats mate/nonmate child; draw child does not become a win.
- Child prefix descent needs prepend, not snoc alone. Verify exact index k+1 and
  actual histories; using only erased endpoint reachability would lose counts.
- Winning-side optional claims could safely be declined. This certificate excludes
  all raw claims anyway, a disclosed stronger sufficient condition, not necessity.
- All-colour/promotion/flag statement is conditional on raw admitted history; it
  supplies no arbitrary-seed FIDE history witness or numeric KRK bound.
- No claim that the universal all-raw-prefix repetition bound holds on a particular
  KRK input, even when a chosen winning tree might be safe. Failure of this strong
  hypothesis gives no draw theorem and no full rule-aware outcome coverage.

Induction directly on the frozen MateWithin recurrence is complete; its witnesses
supply selected moves and all defensive continuations without separate tree data.
The two safety hypotheses descend along actual appends by checked clock arithmetic
and prepend. No mathematical gap identified in this exact conditional argument. LOCAL_VERIFIED;
Gate F pending. Frozen interface and proof sources inspected before Lean.
No independent external review/enumeration/oracle/per-position certificate or full-
game run. Full FIDE correspondence, KRK strategy/distance coverage remain open.
