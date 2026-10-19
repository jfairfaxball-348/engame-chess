# Working rules for agent sessions (Codex, Claude Code and others)

## Always commit, push and merge
Every session ends with its work on `main`. No session leaves work only on a feature branch.
1. Commit every change (clear message; session ID in the subject, e.g. `S002: …`).
2. Push the session branch: `git push -u origin <branch>`.
3. Merge into `main` and push `main` (fast-forward when possible, else a merge commit; never force-push `main`).
4. Before starting, `git fetch origin` and start from the latest `main`. If an earlier session's branch was never merged, merge it first. "Run next session" means the prompt in `NEXT_SESSION.md` **on `main` after that merge**.

Pushing or merging never upgrades a claim: a Lean build, CI run or audit counts as passed only if its result was actually observed.

## End every session with the progress table
At the end of every session, update `docs/SESSION_PROGRESS.md` from the actual proof evidence and reproduce its progress table in both the written session closeout and the final reply to the owner. This applies even when a session makes no mathematical progress.
- Keep the same columns and baseline row order: K vs K; K+B vs K; K+N vs K; K+R vs K; K+Q vs K; K+P vs K; all four-, five-, six- and seven-piece endgames; **full Syzygy parity (through seven pieces) last**. Piece totals include both kings. The grouped rows cover every material class at that size; add individual class rows when useful without dropping the aggregate rows.
- Use short, evidence-based entries for progress and remaining work. Distinguish frozen results, formally verified results awaiting freeze, partial results and open work. A local forcing family does not complete a material class.
- Below the table, give one sentence saying what changed this session, or explicitly say that mathematical progress is unchanged. Do not invent completion percentages or equate theorem counts with solved classes. Syzygy parity requires complete outcome coverage and the relevant WDL/DTZ rule and distance semantics.

## Lean library rules
- **One module per theorem** under `formal/EndgameChess/`. Shared definitions go in separate modules and are imported. Add each new main declaration to `formal/AxiomCheck.lean`.
- **Never edit a frozen theorem's module.** Corrections go in a new module or version (see `docs/PROOF_PROTOCOL.md`).
- **Verify only what is an obligation:** the modules you changed and their importers. Local `lake build` and CI are incremental. Don't re-run clean-checkout verification of other theorems; that is done once per theorem at Gate F/Z.

## Research rules
Follow `docs/PROOF_PROTOCOL.md` and the active prompt in `NEXT_SESSION.md`. No tablebases or engine oracles. `theorems/LEDGER.csv` changes only at Gate Z.
