# EC-C034 — Excluding raw current and every intended threshold

S056, 2026-10-20. Classical bookkeeping certificate, no novelty claim.

## Definitions and exact claim

RawClaims.CurrentThreshold s := 100 ≤ RawClock.clock s.trace OR
3 ≤ RawRepetition.currentOccurrences s.
IntendedThreshold s := ∃ actual Move m, ∃hm:isLegal(erase s)m=true,
CurrentThreshold(append s m hm).
AvailableThreshold s := CurrentThreshold s OR IntendedThreshold s.
These NEW predicates are raw bookkeeping, not certified FIDE CanClaim or a lawful
adjudication instance. Frozen generic Layer.CanClaim is unchanged.

Every raw State s, if (1)clock(s)+1<100, (2)currentOccurrences(s)<3,
and (3)for EVERY m and actual legality proof hm,
occurrences s.trace (play(erase s)m)<2, then ¬AvailableThreshold s.
No side/material/terminal/history restriction, no adverse intended move omitted.

## Complete proof

Root clock<100 follows from(1), so neither current clock nor current repetition
threshold holds by(2). For ANY m/hm, frozen append_clock_le gives childclock ≤
rootclock+1<100. Frozen append_currentOccurrences gives childcount = old full
history queried at NEW endpoint key +1. By(3) this is <3. Thus neither threshold
holds at ANY actual legal child, refuting IntendedThreshold's existential. The
root and child exclusions refute AvailableThreshold's disjunction.

## Audit boundaries and sources

At child queried count2 gives childcount3, so premise <2 is essential, not≤2.
At rootclock99, root+1<100 fails, protecting intended-100 claims; clock98 permits
child≤99. Current root count hypothesis independent of child query hypothesis.
Zeroing resets can lower childclock and satisfy the bound; no list truncation.
No legal replies makes intended existential false and universal hypothesis
vacuous, but root conditions remain required. Pseudo-only moves lack hm and do
not enter the legal intended predicate. Counts use exact full normalized keys,
all actual promotion/colour/flag/castling/EP moves and stored history retained.
No strategy-tree witness, uniform numerical KRK bound or actual arbitrary-clock
win follows from explicit hypotheses. No concrete full-game diagnostics.

Sources: frozen RawClock.StepBound, RawRepetition.CurrentAppend and definitions,
S032 specification. No FIDE key/rights-history correspondence, successful claim
protocol, no-earlier-terminal admissibility, automatic draw/mate precedence,
strategy lifting, WDL/DTZ or solved material class claim. No enumeration/oracle.
