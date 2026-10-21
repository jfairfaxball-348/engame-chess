# Endgame Chess — working instructions

## Objective and priority
Work towards proof-based endgame lookup-table parity through seven pieces, one material class at a time, as defined in [the charter](docs/CHARTER.md). The distant aspiration is an ultra-weak proof that the normal chess starting position is drawn; it is NOT established. Do not query tablebases, use a chess engine as a proof oracle, or certify outcomes by copying enumerated position values.

**Current material class: KRK.** Complete its outstanding full-history/rule-aware outcomes and distances before moving to KQK. See [current work](NEXT_SESSION.md) and [KRK frontier](research/KRK_POSITIVE_CLOCK_FRONTIER.md). Do not confuse frozen supporting lemmas with an entire solved material class.

## How to work
- **Research continuously, especially on the owner's laptop.** A session is merely available work time, not a unit of proof, review or publication. Continue through multiple lemmas, tests, formalisation steps and commits when useful. No mandatory session IDs, session closeouts, handover reports, separate freeze sessions, or end-of-session tables.
- Keep working on the highest-priority **open obligation** of the active material class. Necessary supporting lemmas and diagnostics are welcome when they materially advance it. Don't chase easy theorem counts or endlessly generate infrastructure.
- Start from current code, preserve existing results, and commit coherent changes as useful. Push to main when work is ready to share. Neither a commit nor a merge marks mathematical completion. No per-session branch, mandatory merge ritual or forced publishing cadence.
- Run relevant local checks when source changes. Lean builds and focused tests are more useful than repeated clean builds of unchanged theorems. Do not interrupt mathematical research just to issue another status report.
- Keep [NEXT_SESSION.md](NEXT_SESSION.md) as a **short optional live bookmark** of the current obligation, blockers and useful entry points. Edit it only when the mathematical direction or next obligation actually changes; it is not an approval gate and needs no full successor prompt.
- Update [the roadmap](docs/ROADMAP.md) only at a meaningful material-class milestone or actual change of scope. No mandatory progress chart and no session diary.
- Existing sessions/ and their evidence are **historical archives**, not templates or required deliverables. Do not add to them merely because an interactive session ended.

## Preserve mathematical integrity
- State exact rules, assumptions, quantifiers, and what is proved: possible mate, forced mate, actual draw, outcome, or distance. A local winning family is not global KRK closure.
- Work from a sound mathematical argument, challenge its boundary cases, then formalise in Lean. Disallow `sorry`, `admit`, hidden axioms, unsafe proof escapes, and unwarranted transitions from diagnostic computation to theorem.
- Prefer a separate Lean module per mathematical result; reuse shared definitions and keep `formal/AxiomCheck.lean` current for new public main declarations.
- **Never silently edit a frozen proof.** Keep the immutable manifests and [theorem ledger](theorems/LEDGER.csv). Freeze a result only with a checked paper-to-Lean correspondence, successful reproducible Lean build, acceptable axiom report, and a pinned source commit. The minimal requirements are in [PROOF_PROTOCOL](docs/PROOF_PROTOCOL.md). A freeze may happen in the same work session as its proof, after verification.
- Existing frozen proof modules, manifests, and source commits are historical evidence; do not delete or rewrite them to simplify documentation.
- Speak honestly about actual executed checks and unresolved obligations. Do not claim CI/Palomar success unless observed.

## Owner direction
The October 21 owner request removes former per-session bureaucracy and reporting duties. This **does not itself resume** the KRK research run that the owner previously stopped after S092; subsequent local work or an explicit 'run next session' instruction authorises work on the KRK obligation without requiring an S093 ceremony. Do not start KQK until the owner selects it.
