# Next work — KPK geometric classification

**KRK is complete** under the [outcome target](docs/CHARTER.md#parity-target-hard-boundary-owner-2026-10-29).
See [KRK status](docs/KRK_COMPLETION.md).

**KQK is complete and frozen** as [EC-T0050](theorems/frozen/EC-T0050/v1.md):
every locally legal fresh position, both colours and turns, independent
actual winning/holding, dead/live, and sufficient 97/98-ply bounds.
See [status](docs/KQK_COMPLETION.md) and [proof](proofs/KQK_FRESH_WDL50.md).

Clean-source verification passed: 501-job build, 170 new public theorem
axiom reports, standard permitted axioms only. Proof source is pinned in
the manifest. No further KQK closure obligation remains.

The owner authorised continuous **KPK** work under the
[plan](docs/KPK_PLAN.md). Continue with the explicit geometric win/hold
partition outside the proved exposed-pawn/rook-pawn-fortress draw regions
and the proved seventh-rank support bands. Safe quiet king entry and
all three support squares for a sixth-rank non-rook pawn are proved.
Bishop and centre pawns on the sixth and seventh ranks are now classified in
`Rules/KPK/Coord`, apart from a stalemated lone king on the sixth rank. The next
obligation is the fifth rank: finish the guard from the race lemmas in `Coord/Race`,
`Five` and `Five2`, then the winning plan, then lower ranks, knight pawns and rook
pawns. General dead/live and
the no-limit comparison also remain open. The [partial proof](proofs/KPK_WDL50.md)
maps the existing Lean results and exact gaps. KPK is not complete.

The pawn/promotion interfaces, universal strong-side holding, no
unpromoted mate, major-promotion continuation with retained KPK history,
and the all-rank rook-pawn corner fortress are available. Build on these
and the supported-seventh 99/100-ply wins and seventh-king/sixth-pawn
101/102-ply classification, including its exact corner-stalemate/dead
exception. Centered support now wins in 103/104 plies for both turns;
`KPK.fresh_key_band_wdl50` unifies the
three support squares. The proof source maps the exact declarations.
Continue without intermediate freeze or closeout.

The target remains fresh WDL50 and dead/live for every legal position,
both colours and turns. Exact M4/Mn/DTM/DTZ catalogues, arbitrary incoming
clocks/histories and other classes are outside scope.
