# S033 adversarial paper review — EC-C022

Same-agent adversarial review completed before new Lean source was written;
not independent external review. Paper: `proofs/EC-C022_RULE_LAYER_PROJECTION.md`.
The precise abstract theorem has no remaining local argument gap. This is a
Gate L review of the generic implication, not the concrete FIDE history layer.

| Attempted falsification | Resolution |
|---|---|
| Budget zero but defender has a claim | The only zero-ply target is exact frozen MateGoal. A future concrete model checks actual terminal mate before further actions. No claim guards a terminal goal here. |
| Wrong named colour | Goal is exactly MateGoal σ (erase s); no colour change or “someone mates” substitute. |
| Empty defending move set | Explicit witness required. No vacuous universal branch can prove a nonterminal win. |
| Any live position treated as winning | Ongoing nondeadness is only a guard; chosen/universal recursive certificates are still required. |
| Child ends immediately in draw | Child remains a BoardStep; the interface cannot prune it. A correct concrete draw child has neither goal nor Ongoing, so no recursive certificate. |
| Hidden defender reply missing after erasure | Completeness is quantified over EVERY raw Legal successor at ongoing states, separately from winning premises. Proof fixes an arbitrary r before choosing its lift. |
| Only cooperative reachability proved | The proof retains the entire universal reply branch and exactly the same n; no path-existence replacement. |
| Assumed projected strategy in interface | Fields A–C contain only Legal, erase and DeadK facts. They never mention MateWithin, RuleMateWithin or a winning continuation. |
| An extra axiom supplies A–C | These are quantified hypotheses/proof fields. The identity/no-claim mathematical instance witnesses consistency; no Lean axiom declarations are needed. |
| Clock-free win lifted back without budget | No converse; current or intended claims can spoil it. S032's extra clock/repetition certificate is not used as a premise here. |

Concrete reason completeness matters: White Kh8/Rb2, Black Kb1, Black to move
has a legal rook capture Kxb2 to dead KK, as well as noncapturing replies (Ka1
and Kc1). After any noncapturing legal reply, the frozen strong-arrival KRK
theorem wins for White. Removing only the capture reply at a tagged root and
using the identity layer thereafter would create a false White forcing result
at the root; finite raw branching combines the noncapture bounds. This is a
paper failure analysis of a malformed interface without B, not a newly compiled
counterexample or a global-history claim. B forbids exactly that omission.

All induction obligations were checked: base goal, successor terminal goal,
strong chosen-move soundness, weak witness soundness, weak universal lifting,
nondeadness, turn equalities and unchanged child budget. No finite-X assumption,
KRK theorem or board enumeration is needed by the actual projection proof.
Existing frozen modules/records must be imported unchanged. Gate F remains
pending until exact-source build and axiom evidence exist.
