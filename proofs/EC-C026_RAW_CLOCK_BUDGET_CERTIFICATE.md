# EC-C026 — Conditional raw prefix and prospective-ply clock certificate

S040, 2026-10-20. Classical arithmetic consequence of the frozen EC-T0023
actual-trace growth theorem. No novelty claim, new FIDE encoding, tablebase,
engine, enumeration or stored-position certificate. Sources: EC-T0021/0022/0023
unchanged definitions and proofs, S032 rule/distance specification §5.

## Exact statement and domain

Every state is the frozen RawTrace.State with full initial-rooted trace data;
clock is the frozen halfmove fold. Extends k s u means exactly k actual legal
append operations, retaining the prior trace and each Move/legality witness.
RawBoardStep u v means an actual one-move append, not merely related erasures.
All counters and indices count BOARD PLIES. The literal 100 is the intended
fifty-move threshold in plies; no claim/adjudication predicate is defined here.

For EVERY s:State and n:Nat, assume the explicit hypothesis

    clock(s.trace)+n < 100.

Then for EVERY k:Nat and u:State such that k≤n and Extends k s u:

    clock(u.trace)<100 ∧
      (k<n → ∀ v:State, RawBoardStep u v → clock(v.trace)<100).

Quantifiers over s,n,k,u and prospective v are universal. No chosen strategy,
material, side or endpoint outcome enters. The second conjunct includes EVERY
legal prospective move at an interior prefix, even a move outside a selected
strategy and a reset/draw-ending child. It bounds the computed prospective
child without asserting that this announced move is actually played.
The first conjunct includes k=n; the second requires k<n. No conclusion is
claimed for a further move from depth n. n=0 still bounds the exact root.

The budget inequality is a HYPOTHESIS, never a promised certificate for KRK.
There are no arbitrary clock seeds, independent endpoint-clock premises,
ReachK surrogates, new terminal guards, or pruning of adverse legal children.
No extra shared definitions, arithmetic lemmas, prefix-extraction or exact-length
theorems are required. One combined main theorem suffices.

## Proof

Fix s,n and the budget inequality. For arbitrary k≤n and Extends k s u,
frozen clock_le_extension gives clock(u.trace)≤clock(s.trace)+k.
Addition monotonicity gives clock(s.trace)+k≤clock(s.trace)+n<100.
Transitivity proves the first conjunct.

If k<n, take ANY v with RawBoardStep u v. The unchanged Extends.snoc
constructor gives Extends (k+1) s v using that actual edge. Naturals satisfy
k+1≤n. Apply frozen clock_le_extension to this actual extended trace and
addition monotonicity to conclude
clock(v.trace)≤clock(s.trace)+(k+1)≤clock(s.trace)+n<100.
There is no quietness premise: frozen growth already includes zeroing moves.
Complete stored history is retained by the unchanged append relation.

## Symbolic boundary controls

At n=0, k≤0 forces k=0; Extends zero retains exactly s. The budget gives
clock(s)<100. k<n is false, so no prospective bound is asserted.
At k=0 with n>0, every actual legal first append is covered. At k=n the
current bound remains, while another ply may consume a budget not included
in n. In particular, a hypothetical endpoint counter 99 and quiet next edge
would reach 100; no initial-rooted realization of that example is asserted.
Thus replacing k<n with k≤n would invalidate the unrestricted arithmetic argument.
A sum of 99 satisfies the strict premise; a sum of 100 does not. The theorem
makes no assertion when the premise is absent, including h=99,n=1.

One quiet edge increases by exactly one; a zeroing edge resets to zero; mixed
paths use the same universal frozen bound. Equal erased boards do not identify
histories because Extends/RawBoardStep relate full data states. A raw earlier
draw is no extra guard: raw legal continuation is still covered, without
claiming lawful FIDE continuation. All controls are symbolic, not finite tests
or claims to have run initial-rooted promotion/ep/castling/threshold histories.

## Limits

This is the CLOCK side of a possible sufficient-budget argument only. No FIDE
CanClaim predicate is proved false. Repetition counts/key correctness,
no-earlier-terminal admissibility, current/intended claim semantics, automatic
fivefold/75-move adjudication, mate precedence, a full Layer A/B/C instance,
strategy-tree extraction/coverage, rule-aware lifting, numerical KRK mate bound,
holding/outcome, DTM/DTZ/WDL/Syzygy parity and initial-position value remain
separate. Full preceding history and every defender's repetition/intended
claims require further work. No new solved class or frozen ledger row follows.
Existing owner-reviewed FIDE-to-kernel trust boundary is unchanged.
