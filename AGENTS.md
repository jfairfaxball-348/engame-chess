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

## Work only on direct obligations of the active target
Owner instruction (2026-10-21). This rule applies to EVERY research session and
every subsequent target: KRK now, KQK when the owner selects it, and later
material classes. It is not a KRK-only exception. The latest owner instruction
and live roadmap determine the active target; do not advance to another target
without the required owner direction.

1. **Choose the highest-priority open closure obligation.** State its exact
   missing claim, input domain and completion criterion before starting work.
   Research, diagnostics and formalisation must directly discharge that claim
   or a necessary step in its chosen proof. Carry an unresolved obligation
   across sessions; do not replace it with an easier result.
2. **Foundational lemmas are an exception requiring necessity.** Before starting
   one, record the named direct proof step that needs it, the smallest missing
   statement, why existing results cannot supply it, and precisely how it will
   be used to advance the active obligation. Necessity means needed by the
   selected direct proof route, not a claim that every possible proof needs it.
   Include an exit criterion returning immediately to that direct proof.
   Merely being useful, reusable, interesting or easy to formalise is insufficient.
3. **Keep prerequisite work minimal.** Reuse existing results. Prove only the
   scope needed by the admitted direct step; do not extend a prerequisite into
   general library development or another prerequisite sequence without
   establishing its necessity again. A needed prerequisite may be substantial;
   explain the dependency rather than choosing work by theorem size or count.
4. **Local cases and diagnostics must serve the full obligation.** A terminal
   example, restricted family or counterexample is admissible when it resolves
   a necessary case or tests a specified step of the direct proof. It is not
   a substitute for the quantified claim. Do not spend successive sessions
   formalising isolated examples while leaving their integration into the
   main proof unspecified. A failed policy rejects that policy, not the target.
5. **Verification supports research; it does not select the agenda.** Required
   paper/audit/Lean/build/freeze gates still apply, with no weakened evidence.
   Perform the checks required for the result being certified. Do not choose
   extra foundations, refactoring or repeated verification merely to produce
   an easy milestone when the principal mathematical obligation is unresolved.
6. **Report closure-obligation movement explicitly.** The session record and
   progress chart must name the immediate blocker and say which direct
   obligation was closed, narrowed, or left unchanged, with its actual coverage.
   Separate supporting lemmas from new outcome/distance coverage. If the
   headline remaining obligations did not move, say so; theorem/freeze counts
   and additional examples cannot stand in for that movement.
7. **A session boundary is not a stopping instruction.** When the owner says
   to continue until a target is closed, finish the required session records
   and publishing, then continue the next direct obligation. Do not end the
   run merely because a session, lemma, verification gate or milestone finished.
   Unresolved mathematics must remain open and be carried forward. Stop on
   actual target closure, an explicit owner stop/change of scope, or a concrete
   dependency requiring unavailable owner input or external action; state that
   dependency precisely and continue any independent authorised direct work.

Explicit owner requests for repository rules, reporting or tooling are handled
as requested. Record them as governance/support work, not mathematical progress.
The admission record is specified in [PROOF_PROTOCOL](docs/PROOF_PROTOCOL.md).

## Current research priority: direct KRK closure
Owner direction (2026-10-20): follow [the short-term KRK roadmap](docs/KRK_COMPLETION.md).
Quantitative KRK strategy, strategy-specific repetition/history control, complete
rule-aware outcomes and distance correctness are the priorities across sessions.
Apply the repository-wide direct-obligation and necessity rules above. A blocked
direct proof is recorded honestly and carried forward. Freeze checks remain
mandatory but do not set the research agenda by default.
Earlier owner instruction (2026-10-21): run the next session and keep going
until KRK is closed. This explicitly resumes S077 and subsequent KRK sessions,
superseding the 2026-10-20 pause. Preserve all proof and freeze gates and report
open obligations honestly. Do not start KQK under the current direction.


## Latest owner stop overrides the continuing run
Owner instruction (2026-10-21): "finish up here and closeout cleanly".
Close S092 and publish its records; stop the continuing KRK run with KRK OPEN.
The earlier keep-going instruction is superseded. S093 is FUTURE / UNEXECUTED
and requires explicit owner resumption. The direct-obligation and necessary-
prerequisite rules remain applicable when research resumes. Do not start KQK.
