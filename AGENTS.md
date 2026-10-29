# Endgame Chess — working instructions

## Objective
Reach **Syzygy parity** through seven pieces, one material class at a time, by general proofs formalised in Lean ([charter](docs/CHARTER.md)). Parity is a hard boundary: exact WDL50 and DTZ50 for fresh positions (clock 0, no history, no castling rights). Do not pursue stronger rule/history results. The distant aspiration (chess is a draw) is NOT established.

**Current class: KRK.** WDL is done; exact distances remain. See [current work](NEXT_SESSION.md) and [KRK status](docs/KRK_COMPLETION.md). Do not start KQK until the owner selects it.

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
