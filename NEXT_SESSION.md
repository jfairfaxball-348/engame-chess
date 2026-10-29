# Current work — certify and freeze KQK

**KRK is complete** under the [outcome target](docs/CHARTER.md#parity-target-hard-boundary-owner-2026-10-29).
See [KRK status](docs/KRK_COMPLETION.md).

The complete fresh KQK proof is assembled and checked in Lean:
`KQK.fresh_wdl50`, independent actual winning/holding policies,
`fresh_dead_iff`, and sufficient 97/98-ply bounds.
See [proof](proofs/KQK_FRESH_WDL50.md).

The active obligation is final clean-checkout verification, axiom/source
audit and freeze under the [minimal protocol](docs/PROOF_PROTOCOL.md).
Do not declare the class frozen before that evidence is recorded.

The target is every fresh legal position, both turns and colours, with a
proved upper bound sufficient for the 50-move rule. Exact distances such
as M4 are explicitly out of scope, just as the unfinished longer-distance
catalogue is not a gate for completed KRK. Do not pursue incoming clocks,
histories or another material class. Do not start KPK without owner selection.
