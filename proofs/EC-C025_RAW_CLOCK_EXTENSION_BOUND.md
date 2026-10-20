# EC-C025 — Raw multi-step clock growth along actual trace extensions

S038, 2026-10-20. Classical induction on finite paths; no novelty claim.
Sources: unchanged EC-T0021 RawTrace definitions/append_spec and EC-T0022
RawClock fold/append_clock_le, at the separate anchors recorded in their
manifests; S032 specification §5 sufficient-budget discussion. No new rules
interpretation, engine, tablebase, enumeration or per-position certificate.

## Exact definition and quantified statement

Use the frozen initial-rooted RawTrace.State, whose trace stores every actual
Move and source legality proof. Define Extends : Nat → State → State → Prop:

- refl(s) : Extends 0 s s;
- snoc : Extends n s u → RawBoardStep u t → Extends (n+1) s t.

There are no other constructors. RawBoardStep u t supplies an actual Move m,
a proof hm:isLegal(erase u)m=true, and equality t=append u m hm.
Thus the zero case retains the SAME complete raw state, not just its erasure;
each successor preserves the complete prior trace, including before resets.
The n index counts actual appended BOARD PLIES, never full moves or claims.
No clock data, material class, chosen side, strategy, terminal test or arbitrary
root is a premise. Equal erased boards do not identify two stored histories.
Although Extends is a proposition, its endpoints remain the frozen data states;
its step witnesses constrain the actual appended trace, not merely Legal boards.

Main statement, for EVERY n:Nat and s,t:State:

    Extends n s t → clock(t.trace) ≤ clock(s.trace) + n.

The clocks are computed from the stored traces, not independently supplied.
We add no move-length or prefix-bound declaration: the two constructors already
express finite prefixes, and the same theorem applies to each subderivation.
Frozen append_spec gives exact one-move prefix/length retention at every edge;
no extra length field is assumed. Extends has precisely n actual steps by its
constructors, irrespective of any endpoint counter reset.

## Proof

Induct on the given extension. At refl, t=s and n=0, so the conclusion is
clock(s.trace) ≤ clock(s.trace)+0, by reflexivity and addition by zero.
At snoc, the induction hypothesis gives clock(u.trace) ≤ clock(s.trace)+n.
Extract m,hm and t=append u m hm from RawBoardStep. The unchanged frozen
append_clock_le gives clock(t.trace) ≤ clock(u.trace)+1, for EVERY legal m.
Monotonicity of addition and transitivity give
clock(t.trace) ≤ (clock(s.trace)+n)+1 = clock(s.trace)+(n+1).
This includes resets: their child clock is zero and hence satisfies the
one-step bound without any quietness hypothesis. No edge is pruned.

## Symbolic adversarial controls

For n=0 only refl is possible, so t must be s itself. One quiet legal edge
increments exactly once by frozen append_clock, achieving equality. One
zeroing legal edge gives zero ≤ clock(s.trace)+1. Mixed quiet/reset paths
satisfy the same inductive argument: resetting can lower the value but cannot
violate the upper bound; history retention and step count are unaffected.
The extension cannot jump to another history merely because the board matches.
For each actually represented prefix Extends k s u the theorem gives the same
bound with k. This observation does not assert a separate prefix-extraction
interface for arbitrary k; no such theorem is needed here.

An earlier raw draw imposes no new guard: whenever the kernel still permits a
legal append, the raw bound still applies. This deliberately does not assert
lawful continuation of a FIDE game past its terminal point. All controls are
general symbolic arguments. No particular initial-rooted promotion, en-passant,
castling, or long draw-threshold game prefix was constructed or run.

## Limits

This is one prerequisite, NOT sufficient-budget lifting. h+n<100 remains a
future certificate HYPOTHESIS; this theorem does not supply n, a numerical KRK
mate bound, a repetition certificate, or absence of a defender's intended-move
claim. Full-history no-earlier-terminal admissibility, repetition-key correctness,
current/intended claims, automatic fivefold/75-move adjudication, mate precedence,
full Layer A/B/C instantiation, holding/outcome theorems, DTM/DTZ/WDL/Syzygy
parity and initial-position value remain separate obligations. There is no
new solved material class, freeze, or ledger row. Existing FIDE-to-kernel
encoding and official Lean kernel/standard axiom trust boundary are unchanged.
