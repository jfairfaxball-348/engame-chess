# EC-C039 — Same-budget raw lifting under clock and full-prefix repetition bounds

S066, 2026-10-20. Reviewed against frozen EC-T0036 before any Lean.
Classical conditional strategy transport; no numerical KRK witness or novelty.

Use concrete RAW admitted State/layer from EC-C038. For ANY admitted s, colour σ,
budget n, suppose MateWithin σ n (erase s), clock(s.val.trace)+n<100, and
for EVERY k≤n and EVERY actual raw Extends k s.val t,
currentOccurrences(t)<3. Prove RuleMateWithin rawLayer σ n s, the SAME n.
All raw extensions are quantified, including beyond raw terminal endpoints;
this stronger sufficient certificate is not asserted for all KRK histories.

Prerequisite: an actual step s→u prepends to ANY k-ply extension u→t to give
Extends(k+1)s t. Induct on the stored extension proof: at refl use one snoc of
refl s and the supplied step; at snoc append its last actual step to induction.
This retains exact states, move/witness data and depth, not only erased boards.

Proof of lifting by induction on n, generalising the admitted state. At zero,
MateWithin is named board mate, precisely Layer.Goal, so the same certificate
works. The extra root safety hypotheses are sufficient but unnecessary here.
At successor n+1, named mate again supplies Goal immediately. Otherwise the
clock-free recurrence supplies nondeadness and either a strong chosen Legal
child with n-budget mate, or a nonempty weak Legal reply family ALL with n-budget
mate. In either case there is an actual Legal successor at the parent.
The depth-zero full-prefix hypothesis gives current count<3; the clock budget
gives clock<100. Frozen ongoing_iff then gives parent ongoing (using nondead,
nonempty legal replies, clock<150/count<5).

No raw claim threshold is available at this interior parent. Present clock/count
thresholds contradict the bounds. For ANY actual intended m/hm, append clock is
at most parent clock+1<100, and its one-ply actual extension has current count<3
by the full-prefix certificate (1≤n+1). Thus neither current nor ANY intended
clock/repetition threshold holds. This is stronger than merely excluding current
claims and is independent of whether the move zeroes. Claims are not executed.

For ANY actual raw child t, append clock bound yields clock(t.trace)+n<100.
Any k≤n raw extension from t prepends to a k+1≤n+1 extension from the parent;
therefore every child prefix still has count<3. These are precisely the induction
hypotheses; reset moves are covered by the frozen upper bound, not excluded.
Parent admissibility and ongoing give admissibility of each actual append.

Strong branch: extract its actual Legal m/hm witness, choose that appended admitted
child and apply induction to its clock-free n-budget mate certificate. Weak
branch: preserve a nonempty raw Layer reply using completeness; for EVERY Layer
BoardStep child use raw soundness to obtain the matching Legal reply, its
clock-free certificate, and the descended bounds, then induction. No legal
defence/terminal child is pruned. Weak no-claim follows from the parent proof.
The resulting concrete RuleMateWithin recurrence is exactly satisfied.

No explicit winning-tree datatype/extraction is needed: the frozen MateWithin
recurrence already supplies the existential chosen moves and universal replies
used directly by induction. The universal all-raw-prefix repetition hypothesis
is stronger than safety only on a chosen tree; this is disclosed, not weakened.
Terminal named mate can occur before the budget ends. Other terminal draw children
cannot satisfy the supplied clock-free winning continuation; they are retained
in quantifiers and would refute its premise, not silently removed from moves.

Adversarial obligations: n=0; early mate; strict99/100 bounds; intended claim at99;
count2/3 and new endpoint in old history; zeroing child; every adverse capture to
KK; all colours/promotions/raw flags; actual trace dependence and subtype proof;
no arbitrary history/count seeds; optional winning-side claims may be declined,
but certificate conservatively excludes them too. Root+budget safety fails for
some genuine wins; failure does not prove draw. Relative RAW Layer only, full
FIDE key/rights/history/claim correspondence and all KRK numeric/outcome/distance
coverage remain separate. No WDL/DTZ/initial value, enumeration/oracle/certificates
per position, actual full-game witness or full numerical KRK bound is claimed.
