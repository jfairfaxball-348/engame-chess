# Working rules for agent sessions (Codex, Claude Code and others)

## Always commit, push and merge
Every session ends with its work on `main`. No session leaves work only on a feature branch.
1. Commit every change (clear message; session ID in the subject, e.g. `S002: …`).
2. Push the session branch: `git push -u origin <branch>`.
3. Merge into `main` and push `main` (fast-forward when possible, else a merge commit; never force-push `main`).
4. Before starting, `git fetch origin` and start from the latest `main`. If an earlier session's branch was never merged, merge it first. "Run next session" means the prompt in `NEXT_SESSION.md` **on `main` after that merge**.

Pushing or merging never upgrades a claim: a Lean build, CI run or audit counts as passed only if its result was actually observed.

## Research rules
Follow `docs/PROOF_PROTOCOL.md` and the active prompt in `NEXT_SESSION.md`. No tablebases or engine oracles. `theorems/LEDGER.csv` changes only at Gate Z.
