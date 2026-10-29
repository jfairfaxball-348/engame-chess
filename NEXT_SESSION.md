# Current work — KRK review and KQK transfer plan

**KRK complete** under the [outcome target](docs/CHARTER.md#parity-target-hard-boundary-owner-2026-10-29): proved win/draw for every position, plus a move bound that fits the 50-move rule. Exact mate counts are optional. See [KRK status](docs/KRK_COMPLETION.md).

**Next task (owner, 2026-10-29): review, not new proofs.** Read the KRK proof library and write a short KQK plan (e.g. `docs/KQK_PLAN.md`) that answers:
1. **What transfers.** Which KRK lemmas carry over to a queen almost unchanged, since a queen moves like a rook plus a bishop, and which need restating? Look first at the wall/box/forcing modules (`Rules/KRKForcing`, `Rules/KRKBox`, `Rules/KRKCentral`), rook safety (`KRKForcing/CaptureSafety`, `OutcomeClassification`), dead/live (`Rules/KRKLive`) and the 50-move bridge (`KRKCentral/Fresh*`).
2. **What's new for KQK.** Stalemate traps (the queen covers far more squares), queen safety against the lone king, and the shorter mate bound.
3. **Generalise or copy.** Where a lemma could be stated once for any "line piece" (rook directions, queen directions) so that KRK and KQK both follow from it, without editing frozen modules.
4. **Expected effort, with KPK in view.** KPK will need the KQK result, because a promoted pawn becomes KQK. It will also need draw/holding strategies (key squares, opposition) and pawn/promotion/clock-reset rules. The rules kernel already models pawns and promotion (`Rules/Board.lean`).

Keep the plan short and concrete. Starting KQK proofs needs the owner's go-ahead after the plan.
