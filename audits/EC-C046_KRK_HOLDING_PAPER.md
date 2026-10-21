# EC-C046 — adversarial paper audit (S078)

Separate same-agent audit after the standalone paper and before Lean. This is
not independent external review. Reread actual RuleMateWithin recurrence,
RawHistoryLayer.State/layer, raw claim thresholds, typed append guard, universal
KRK potential and both original termination audits.

* Terminal/zero paths: RuleHold checks the zero prefix, so a root already mated
  against c cannot hold. A drawn terminal does hold with a policy whose values
  there are irrelevant. No ongoing move is manufactured at fuel0; child
  admission forces ongoing parent and strict descent refutes this branch.
* None is only a correct current/intended CLAIM at an ongoing own turn, never a
  pass. At other turns/terminals it is inert. Opponent claims end in a draw and
  need no appended state. Own claim at a position with a possible mating move
  also draws if chosen; this is legal holding. Unavailable claim cannot be
  chosen. A putative opponent winning certificate explicitly rules out the
  holder's claim, which is essential in the converse.
* Uniformity: individual child forcing certificates cannot be given a common
  budget merely by assertion. Strong induction on existing fuel saturates EACH
  at P(child), universally <=P(parent)-1. This proves exactly the bounded
  all-reply interface needed for defensive choice, without child enumeration.
* Policy is globally legal on every ongoing own-turn state, including those
  outside the safe KRK Region, using arbitrary actual replies there. Safety
  invariance is asserted only from Region and full opponent nonforcing. This
  avoids defining a partial strategy with no off-branch legal action.
* Every actual opponent board child remains, including immediately drawn/dead
  children, bad strong moves, castling and rook capture. Typed RAW histories
  retain initial/prior/current positions, real counters, rights and ep. No
  noRights, low-clock, histogram, rook-safety or chosen-strategy premise enters.
* Saturation at terminal Region endpoints includes material outside KRK, but
  those endpoints admit no board steps. Immediate goal at any budget remains
  valid. Mate at clock150 stays mate; no fuel0=>draw inference is made.
* Converse is about ANY holding policy and EVERY finite opponent certificate.
  Prefixing transfers all-path safety at the selected child. Opponent chooses
  its existential move; holder chooses its actual Some move under no-claim;
  certificate's universal branch covers that same move. No cooperation used.
* Maximal COMPLIANT path can end ongoing when own policy chooses a claim. Such
  a path is not falsely called a maximal unrestricted board path. Its claim
  must be executed to form the complete stopping action. An arbitrary short
  compliant prefix need not be terminal. Opponent claims can stop even earlier.
* Classical choice here proves existence of a history policy, not a stored
  position table, exhaustive class proof or executable oracle. Full admitted
  RAW holding duality does not evaluate the forcing predicate by a geometric
  formula; full FIDE correspondence, outcome classification and exact WDL/DTZ
  remain open. Failure of the sufficient73 family still proves no draw.

Verdict: the stated RAW holding equivalence and bounded stopped-policy play
close on paper. EC-C046 LOCAL_VERIFIED for this exact statement, formal/freeze
gates pending. Return to direct KRK outcomes after this dependency; no class
closure or full FIDE interpretation is established by the equivalence.
