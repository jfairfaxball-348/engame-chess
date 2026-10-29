# Current work — KQK complete; await owner selection

**KRK is complete** under the [outcome target](docs/CHARTER.md#parity-target-hard-boundary-owner-2026-10-29).
See [KRK status](docs/KRK_COMPLETION.md).

**KQK is complete and frozen** as [EC-T0050](theorems/frozen/EC-T0050/v1.md):
every locally legal fresh position, both colours and turns, independent
actual winning/holding, dead/live, and sufficient 97/98-ply bounds.
See [status](docs/KQK_COMPLETION.md) and [proof](proofs/KQK_FRESH_WDL50.md).

Clean-source verification passed: 501-job build, 170 new public theorem
axiom reports, standard permitted axioms only. Proof source is pinned in
the manifest. No further KQK closure obligation remains.

The target is every fresh legal position, both turns and colours, with a
proved upper bound sufficient for the 50-move rule. Exact distances such
as M4 are explicitly out of scope, just as the unfinished longer-distance
catalogue is not a gate for completed KRK. Do not pursue incoming clocks,
histories or another material class. Do not start KPK without owner selection.
