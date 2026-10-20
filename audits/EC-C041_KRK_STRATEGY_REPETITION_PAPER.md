# EC-C041 — adversarial paper audit (S070)

2026-10-20. Separate same-agent review after standalone paper; not independent
external review. Reviewed frozen key_legal_congr, key/normalizeEP definitions,
MateWithin/ForceMate and fixed-budget constructors, KRK arrival bound, and the
known raw chase-cycle control. No new executable diagnostic, engine, tablebase,
class enumeration or position certificates.

- Exact dependency admission: blocked KRK repetition/all-defences step, existing
  evidence insufficiency, minimal key-budget interface/payoff and exit back to
  actual traces/incoming history are explicit. The generic lemma is subordinate
  to the stated KRK strategy theorem.
- An arbitrary ForceMate witness is not minimal and does not force a canonical
  decreasing rank. Paper uses the unique LEAST natural budget and proves its
  specification. Core well-ordering suffices; no search table is introduced.
- Default d=0 on losing inputs could falsely suggest mate. Every policy vertex
  and the d=0 converse require ForceMate. Equal-key default cases use Win iff.
- Root key equality preserves board/turn but not raw ep. Frozen congruence yields
  IDENTICAL full played positions on actual legal moves, allowing the direct
  same-budget proof. Neither source ep equality nor full FIDE key iff is assumed.
- Root check/mate preservation includes queried colour, actual legal successor
  sets, empty reply cases and wrong-colour turn. Deadness is not assumed key
  invariant: a common winning child proves nondeadness at the target constructor.
- At a positive minimal budget, invert the exact recurrence. Every weak legal
  child has budget at most parent−1; the reply set is nonempty. Stalemate is not
  won vacuously. Any capture-to-KK would contradict that winning child, rather
  than being removed from the legal relation. Intended weak moves are included.
- Pairwise keys on the entire list follow from all-later strict rank, not just
  adjacent differences. Length counts vertices: ≤d+1 means ≤d plies. A singleton
  may be nonterminal; only MAXIMAL lines must end at mate. Zero-rank winning
  input is actual mate and has no allowed extension.
- New rank-policy choice is distinguished from the frozen geometric policy.
  Unchosen legal winning-side moves can cycle; the known chase cycle therefore
  does not refute the restricted strategy theorem. No claim about every raw
  continuation is made or imported from EC-C039.
- Incoming old-key multiplicity can still enable threefold at the first new
  occurrence. This remains separate, along with actual stored trace extension,
  clock budgets and current/intended claim correspondence. The ceiling508 is
  too coarse for strict50-move certification; no full FIDE outcome or exact
  WDL/DTZ parity follows from a least-budget definition.

Verdict: the exact key-simple finite-rank strategy closes on paper. EC-C041
LOCAL_VERIFIED; formal verification and freeze pending. Rule-aware covered inputs
unchanged. The exit task is actual trace occurrence certificates, not another
unrelated generic prerequisite.
