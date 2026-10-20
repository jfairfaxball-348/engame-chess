# EC-C045 — adversarial paper audit (S076)

Separate same-agent audit after standalone paper, not independent external
review. Read actual play/isPseudo/canCastle/targetOK, ordinary noRights interface,
all-flag lone_move_cases, clock fold/reset/append, dead-KK theorem and stopped
append/ongoing guards. No engine/tablebase/class enumeration or stored position
certificates. Four-part dependency admission serves exact KRK outcome horizon.

- Arbitrary strong castling cannot be excluded by KRK or admitted histories.
  Paper handles the actual king/queen schemas, sole home rook and empty king/
  crossed-rook destination. End material only is needed, not a false ordinary
  StepM representation. Weak-king coordinates remain universally quantified.
- Source pawn is absent; raw ep cannot trigger capture without a pawn. Strong
  legal target is empty because own K/R and enemy K are all forbidden. Ordinary
  and castling strong moves are therefore quiet, regardless of flags.
- Weak retained-KRK branch still has old strong rook at its old square. Occupied
  legal target could only be that rook, but destination then contains the weak
  king, contradicting retained rook. Quietness is derived, not assumed from a
  material-count oracle. KK branch stops by actual deadness even after reset0.
- Bad strong moves giving dead KRK remain legal children and terminal; no safety/
  winning premise or hidden legal-reply pruning. Both turns/all colours/flags.
- RawTrace.Extends may continue after terminals and is not substituted. Typed
  admitted BoardStep's child proof forces parent ongoing through append iff.
  All legal ending children remain admitted from an ongoing parent; no child-
  ongoing filter. Full initial/current/previous trace and actual move retained.
- Potential uses0 for EVERY terminal; it does not call every terminal draw.
  At149 quiet step reaches150 and stops (mate-first priority preserved); reset
  capture reaches dead KK and also stops. Clock≥150 root cannot be ongoing.
  Subtraction used actively only with clock<150, so each step spends≥1.
- Universal bound is over all finite typed paths; maximal endpoint is terminal,
  while truncated prefixes can be nonterminal. Existence uses well-founded
  natural potential and actual nonempty ongoing replies, not defender cooperation
  or a promised winning branch. Claims stop with zero board plies, no claim pass.
- This is termination, not an exact RAW/FIDE outcome or distance. No draw from
  failure of the incoming sufficient histogram or a renamed RuleMateWithin.
  Full FIDE correspondence/holding and exact WDL/DTZ remain separate.

Verdict: exact universal admitted KRK potential/clock termination closes on
paper; EC-C045 LOCAL_VERIFIED, formal/freeze gates pending. Earlier sources and
41 frozen bundles unchanged. If all-flag material formalisation blocks, retain
that exact gap rather than restricting flags or changing the principal task.
