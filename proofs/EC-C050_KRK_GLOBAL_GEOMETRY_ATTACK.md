# EC-C050 — Direct global KRK geometric budget attack

S086,2026-10-21. Incomplete direct attempt; main candidate remains PROPOSED.
No tablebase/engine oracle, exhaustive class proof or stored position results.
Sources are the project's actual quantitative wall/setup proofs and frozen
failed-policy controls. Classical geometry only, no novelty claim.

## Principal target and precise payoff

For each strong colour sigma, prove the actual uniform KRKWallBudget(sigma,B)
for some derived B<=95: every canonical strong-turn strict separating wall,
all flags/all defensive legal replies, actual mate within B board plies.
This is a sufficient route to new class coverage, not a necessary condition
for any possible KRK solution. Frozen parametric setup would give every legal
strong KRK arrival a clock-free B+4<=99 certificate. At a genuine clock0
admitted KRK root, EC-T0046 would then lift it to the same RAW budget and
ActualWin without incoming count premises. Weak setup B+5=100 at B95 does NOT
meet the strict<100 supplied-budget lift; that case cannot be silently included.

No95 theorem has been proved. A failed coordinate policy or conservative upper
bound>95 does not falsify the existential optimal wall-budget claim. Full
arbitrary-clock/history outcomes, full FIDE correspondence and exact global
WDL/DTZ also remain required even if this sufficient route were to close.

## Route A — Recombine the existing per-rank budget

The certified wall proof gives73*n for n=7-rookRank, 1<=n<=6. The maximum438
feeds the certified442/443 setup ceilings. Inserting this into the new lift
does not meet N<100. A prior existential ForceMate proof cannot supply a better
numeral. Replacing438 with95 is a missing theorem, not algebraic simplification.

The proof's finer allowance is U(n-1)+56+4*(g-1)-edgeCredit(n), where g is the
rook/strong-king rank gap, g<=7-n, and edgeCredit(1)=3. As an OPTIMISTIC BUDGET-
ENVELOPE CALCULATION, reinserting only that smaller gap cap yields

    V(1)=73,
    V(n)=V(n-1)+56+4*(6-n), 2<=n<=6.

The numbers are73,145,213,277,337,393. This is a calculation of that scalar
envelope, not a new verified chess bound or a lower bound on optimal mate.
Even its n2 allowance145 exceeds95. Merely tightening the scalar gap cap does
not discharge the requested inequality. All chess strategy/import obligations
would still need a separate proof before even calling393 a certified ceiling.

## Route B — Amortise file pursuit across rank advances

A lower-band pursuit pays f(m)=8*m-6 (m positive oriented distance of the strong
king from a file edge), at most50, plus its exit budget. Within one orientation,
a real king-file advance decreases m and pays its local moves. A global bound
would have to avoid charging the full50 afresh at every raised rook rank.

The attempted potential needs an inequality for EVERY actual post-exit wall,
linking old oriented file progress with the NEW phase's orientation/file offset,
rank gap and paid normalization/rescue. Existing exit/upper-wall interfaces
return a new wall and numerical rank progress, not the needed globally monotone
or paid-reset file potential. The strong king's rank is retained by rank raise,
so some vertical-gap charges can be related; this does not establish the missing
horizontal correlation. Arbitrary orientation reset is not free progress.

Exact missing statement: for a specified new potential Phi and each chosen
geometric phase, exhibit actual legal strong choices and retain EVERY weak
reply, proving (actual phase plies)+Phi(successor)<=Phi(parent), including
upper exits, aligned checks, threatened-rook rescue and file-direction changes.
No such Phi inequality has been closed here. An abstract interface which
forgets successor files cannot be used to assert the required correlation.
This is a proof gap, not a counterexample to95 or to the frozen forcing result.

## Route C — Box contraction and the terminal trap

An alternative design confines the weak king by rook file/rank rays to a
rectangle and hopes to charge each shrink to width+height. It needs explicit
rook safety, strong king nonblocking, actual nonempty weak replies, and a mate
finish. Shrinking a protected box alone is insufficient.

The existing FROZEN kernel theorem protected_corner_reentry_stalemate states:
White Kf6/Ra7, Black Kh8, White turn; Rg7 is legal, the child is not in check
and has NO legal moves. The rook on g7 is protected by Kf6, but the one-square
diagonal confinement of Kh8 is stalemate. This is the project's actual fixed
failed-policy control in KRKForcing/ReentryExamples.lean, not a new engine or
tablebase observation. It refutes the naive protected-box-shrink progress lemma,
NOT the global95 claim. No compatible full initial history/clock0 is inferred
from this local kernel configuration.

Required replacement: an all-reply legal shrink/king-approach/mate alternative
whose invariant rules out nonchecking one-square traps, retains the rook against
all captures, pays all tempos and proves a numeric global potential. Those
alternatives and inequalities remain unproved. Mere area decrease is not mate.

## Selected-policy diagnostic (observed, supplementary only)

A single disclosed clock-free ordinary-move ray-model trajectory tested the
old concrete coordinate policy under an immediate local defensive selector.
It is not a game-value search, class enumeration, tablebase, proof certificate,
or an admitted RAW trace after claim/automatic-draw thresholds. A length>95
falsifies that particular policy's95 bound in the disclosed model only. A shorter
trajectory would not prove its universal95 bound. There is no full initial-history
witness.

Observed root: White Ka1/Rh2, Black Kb3, White turn/no rights in the local model.
The defensive selector inspects only immediate coordinates: lowest rank,
farthest file from strong king, then most interior file on ties, then file order.
There is no game-value lookahead. Observed length109 board plies, ending in
model mate; all109 edges rechecked with the SAME disclosed ray move generator.
Events:7 waits,6 normalizations,31 king-file chases,5 king rank catch-ups and6
checks (55 strong moves plus54 defensive replies). No early mate or capture was
deleted. [Full diagnostic trace](../sessions/evidence/S086/selected-policy.json)
and [executed source](../sessions/evidence/S086/selected_policy.py) retain every
board/move, runtime and source hashes. The imported script's class-enumeration
entrypoint was NEVER called. This is one fixed trajectory, not a class scan.

This evidence shows why simply charging a faster budget to this CONCRETE policy
does not work. It is NOT a counterexample to a better strategy or optimal95,
not a Lean-certified long-play theorem, and not a history-admissible RAW play
through fifty/seventy-five-move draw thresholds. No compatible initial prefix
or choice of independent history counts is asserted.

## Route D — Remove the waiting pairs

The selected109-ply line contains7 waiting pairs. Subtracting14 gives95, but
that is not a strategy transformation: the wait is what forces the weak side
to align, exit upward or open a fixed-direction file gap before a king advance.
Replacing offset-one waits by immediate king-file chasing permits direction
reversals. The FROZEN phase_image_chase_cycle gives the exact legal control:
White Kb2/Rh3, Black Kc4, White turn; Kc2 Kb4 Kb2 Kc4 returns to the identical
full kernel Position after four quiet plies. Both intermediate positions retain
the stated phase geometry and are not opposed. A strictly decreasing board-only
progress measure cannot hold along every move of that naive chase policy.

This rejects simply deleting the paid waits from the existing proof, not every
possible improved king/rook strategy. No RAW infinite play is asserted: actual
clocks/repetitions eventually stop such a loop, which is precisely why clock-
free forcing cannot be promoted to RAW winning by ignoring the delay. Any
replacement must prove an all-reply progress alternative, not grant free tempos.

## Honest frontier

The complete95/all-strong sub100 geometric proof is OPEN. No Gate L pass,
new Lean theorem, Gate F or freeze is justified for EC-C050. Existing46 frozen
bundles and their exact claims remain valid and unchanged. The fresh73 family
is partial; actual strategy equivalences and termination do not evaluate all
remaining low-clock histories or establish full FIDE/global exact WDL/DTZ.
The next substantive obligation is the explicit safe nonstalemating geometric
phase/potential statement above, not another generic bookkeeping lemma.


## S087 substantive phase advance

[EC-C051](EC-C051_KRK_GUARDED_BOX_PHASE.md) supplies an actual guarded NE
width5/6 phase within8 plies with all weak replies, paid crossing escort and
closed endpoint cost inequalities; own-source Gate F passed. A fixed16-ply
kernel cycle shows why blindly extending that phase to width4 fails. The paper
repeated/reflected <=32-ply corollary ends at a small guarded box and is NOT
a newly formalised result or a mate bound. Arbitrary guarded entry, small-box
mating finish and an integrated global sub100 budget remain unproved.
Thus the principal EC-C050 claim remains PROPOSED/open; this is partial direct
geometry progress, not full outcome/FIDE/distance closure.
