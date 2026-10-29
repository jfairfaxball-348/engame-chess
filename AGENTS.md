# Endgame Chess — working instructions

## Objective
Prove the **guaranteed outcome (WDL50) of every position** through seven pieces, one material class at a time, by general proofs formalised in Lean ([charter](docs/CHARTER.md)). That is the hard boundary: fresh positions (clock 0, no history), with a move bound sufficient for the 50-move rule. Exact distance-to-mate is optional, not a gate. Do not pursue stronger rule/history results. The distant aspiration (chess is a draw) is NOT established.

**KRK and KQK are complete** under this target ([KRK status](docs/KRK_COMPLETION.md), [KQK status](docs/KQK_COMPLETION.md)). The owner authorised continuous work on KPK; follow its [plan](docs/KPK_PLAN.md) and [partial proof](proofs/KPK_WDL50.md). Do not start another class without owner selection.

## How to work
- Work continuously on the open obligation. No session IDs, closeouts, handover prompts, status reports or session folders; `sessions/` is a historical archive.
- Prefer general, reusable arguments (formulas, potentials, strategy lemmas that will transfer to KQK) over position-by-position case layers. No tablebases, engines as proof oracles, or position-by-position computed tables as proof, including ones computed in Lean.
- Commit coherent changes and push to main when ready. Run focused Lean builds for changed modules.
- Edit [NEXT_SESSION.md](NEXT_SESSION.md) only when the next obligation changes, and [the roadmap](docs/ROADMAP.md) only at a class milestone.

## Mathematical integrity
- State exactly what is proved (possible mate, forced mate, draw, outcome, distance) and its domain. A local family is not class closure.
- No `sorry`, `admit`, hidden axioms or unsafe escapes. Keep `formal/AxiomCheck.lean` current for new main declarations.
- Frozen modules, manifests and ledger rows are immutable; strengthen via new importing modules. Freeze per the minimal [PROOF_PROTOCOL](docs/PROOF_PROTOCOL.md) (paper-to-Lean correspondence, reproducible build, axiom report, pinned commit).
- Report only checks actually run.
