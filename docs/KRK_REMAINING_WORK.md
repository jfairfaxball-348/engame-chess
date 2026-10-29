# KRK remaining work after the bounded-frontier freeze

2026-10-29. **KRK OPEN.** This report distinguishes the verified supporting
frontier from the remaining class theorem. The executable continuation is
[the next-session prompt](KRK_FINISH_PROMPT.md).

## What is now established

The baseline EC-T0048 proves uniform wall93, strong legal arrivals97 and weak
forcing98, and the actual RAW clock-zero winning criterion on both turns.
Those are upper bounds, not global optimal distances. The older 48 bundles
retain their original statements and trust boundaries.

The new EC-T0049 bundle preserves 213 complete modules and 1,147 public
theorem statements, including the work since the last frozen source. Its
[proof correspondence](../proofs/KRK_BOUNDED_FRONTIER_CERTIFICATION.md) and
[exact inventory](../proofs/KRK_BOUNDED_FRONTIER_SCOPE.json) specify the boundary.
Those counts are source coverage, not a fraction of solved positions.

| Area | Established boundary |
|---|---|
| Board geometry | Complete symbolic iff through weak six/eight/ten/twelve plies, with parity and exact-region subtraction. |
| Strong entries | Immediate mate or ordinary king/rook entry into the previous complete even region, through thirteen plies. Actual short-budget castling exclusions retain native rights and both colours. |
| RAW history-aware outcomes | Every ongoing strong-turn history with `h >= 86`; every ongoing weak-turn history with `h >= 85`, under the exact declarations' KRK/admission premises. Original incoming trace and current/intended claims remain in the formula. |
| Exact bounded winning distances | Strong odd distances through 13; weak even distances through 14. Unrestricted bounded-certificate iff theorems do not by themselves give a compact all-clock classification. |
| Fourteen-ply geometric regions | Complete at every weak square of depth at least two and on the central first strip, including their exact-fourteen additions. |
| Thirteen-ply near strip | Complete canonical near-strip iff and exact-thirteen subtraction. |
| Thirteen-ply inward rays | Necessity at ten horizontal king profiles; constructive universal ray at the high profile only. |

## Open obligations and dependencies

1. **Finish inward thirteen-ply geometry.** Supply constructive ray destinations
   for the remaining nine horizontal profiles, handle transpose, prove the
   complete king-entry/rook-entry iff and exact-thirteen subtraction. Preserve
   square distinctness: the high twelve-ply region alone can include a source
   collision. Entry: `KRKThirteenInnerRook` and `KRKTwelveInnerExact`.

2. **Finish fourteen-ply near strip.** Use the completed thirteen-ply near and
   central profiles, the inward profile and required edge bounds to prove a
   necessary symbolic prison and constructive sufficiency for every surviving
   family. Exclude every other strong move, rook capture, blocked ray and null
   tempo. Subtract the complete twelve-ply region for exact fourteen.

3. **Finish fourteen-ply inward corners and edge.** Include all first-rank/file
   weak squares, central edge cases, both reflections and transpose, terminal
   branches and nonempty legal reply conditions. Assemble a full-board
   fourteen-ply iff and exact-fourteen theorem. `KRKFourteenGeometry` is an
   intermediate all-guard predicate, not that final evaluated classification.

4. **Resolve all remaining clock budgets.** The current complete RAW outcome
   bands leave ongoing strong clocks `1..85` and weak clocks `1..84` outside
   the band theorems; clock zero has its separate baseline theorem. Some such
   states may already lie in earlier partial families. No claim is made that
   every state in these ranges is unknown. Develop compact evaluated regions
   or an analytic optimal ranking with necessity against all legal strong
   choices. Merely extending a sufficient wall bound, renaming a certificate
   or unrolling the mate recurrence does not discharge this obligation.

5. **Arbitrary incoming-history obstruction.** Old keys already seen twice
   can allow current or intended repetition claims. A future key-simple plan
   does not remove those old occurrences. Formalise the paper fixed-barrier
   reduction and least-rank policy if that route is retained, including root
   and mate-leaf exceptions, then actually evaluate its geometric objective.
   Alternatively prove a complete replacement with the same history coverage.
   The current paper reduction is not a Lean theorem and not the answer.

6. **Complete actual WDL.** Produce a total, disjoint White-win/draw/Black-win
   classification for the stated legal history domain, both turns and colours,
   with actual winning strategies and matching holding strategies. Strong
   nonloss and failure of a selected mating policy are not a draw proof.

7. **Finish FIDE-to-model correspondence.** Connect exact board/legal rights,
   repetition-key equivalence and actual history admission to the intended
   FIDE claim/adjudication rules. Preserve optional strong claims, weak current
   and intended claims, automatic draws and mate precedence. Do not call a RAW
   theorem a complete FIDE theorem without this bridge.

8. **Audit terminal and material-exit coverage globally.** Integrate already
   proved mate, stalemate, dead-position and rook-capture-to-KK facts into the
   final theorem's complete domain. Prove there is no omitted branch for
   already terminated histories, legal arrivals or surviving native rights.
   The facts exist in parts; their full class-wide integration remains open.

9. **Exact global distance semantics.** State the required DTM/DTZ and
   rule-aware conventions explicitly, including which player's actions and
   plies are counted, zeroing captures, terminal values, draw values and
   claim-vs-mate priorities. Prove optimal upper and matching lower bounds over
   the entire outcome partition. The 93/97/98 ceilings and exact distances up
   to 13/14 are insufficient for a global exact-distance claim.

10. **Complete aggregate Lean interface and certification.** Give identifiable
    public theorems for total outcomes, strategies, distances and model bridge;
    prove their domains coincide and are exhaustive. Audit exact prose/Lean
    correspondence, build in a clean pinned-source checkout, inspect every new
    main declaration's axioms, then freeze and declare KRK closed only if all
    preceding obligations are discharged. Otherwise report the exact residual
    obligations honestly. KQK remains unselected.

## Practical continuation

Use `C:\engame-chess\formal` with core Lean `leanprover/lean4:v4.35.0`.
The current full local build passes 456 jobs. The certification manifest is
the authority for the subsequently observed clean build and source SHA.
No external CI or Palomar success is assumed. Frozen complete modules are
immutable: new constructive inward results belong in new modules importing
`KRKThirteenInnerRook`; do not extend the frozen file in place.

There is no justified percentage complete or reliable session estimate. The
remaining difficulty is mathematical necessity and history dependence, not
just finishing a known list of routine Lean translations.
