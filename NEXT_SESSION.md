# NEXT SESSION — S028: Force re-entry after the rook checking phase

**Owner instruction:** Execute S028 when the owner says "run next session" or pastes/links this prompt. Follow `AGENTS.md`: fetch latest main, incorporate any unmerged session work first, then finish committed, pushed and merged to main. Publication is authorised. Read `docs/CHARTER.md`, `docs/PROOF_PROTOCOL.md`, the S026 proofs/audits and strategy attempt, S027 closeout, and EC-T0010/0011 manifests before working.

## Starting point and boundaries

Eleven frozen theorem bundles exist; this is not eleven solved material classes. KRK L1 is complete. EC-T0010 proves distant-or-protected all-reply safety. EC-T0011 proves an exact four-ply checking contraction: same-file kings two ranks apart, strong to move, rook at least four files from the lone king and off its rank. Every first reply, chosen king-up, and every second reply is covered; the final position has a distant-rook rank barrier and smaller upper-rank potential, or the first check mates at the edge. Both colours and arbitrary flags are included. Frozen source is `e8daef6daee088c3adaf1c21b51c0a8f1e31103d`, Lean 4.35.0, core only.

The phase need not restore opposition: the kernel-checked Ka2/Rh3/Kc4 return is a counterexample. General clock-free KRK forcing EC-C011 remains PROPOSED. No full KRK WDL, clock/repetition, distance-to-mate, seven-piece parity or initial-position draw claim follows. No engine, tablebase, class-wide enumeration, retrograde solution or per-position certificates may supply the proof.

## Principal mathematical obligation

Prove a finite all-defences re-entry/contraction policy from a precise phase-image family. Do not spend the session repeating forcing definitions or renaming the existing phase as a strategy.

1. Inspect `krk_opposition_four_ply`, `krk_follow_check`, and their supporting reply lemmas at the exact source. In a **new** module importing the frozen modules, first prove the actual image bounds before using them: strong to move; rook one rank above the strong king; lone king one or two ranks above the rook; lone/strong file offset at most two; rook/strong file separation at least four; rook/lone Chebyshev distance at least two. State the relevant `Matches`, `Legal` ancestry, flags and board-bound hypotheses explicitly. If any proposed bound is false, record a local counterexample and repair the family before proceeding. The existing flagship must not be silently strengthened.
2. From the justified family, give an explicit policy leading to actual mate, a correctly oriented EC-T0011 entry, or another strictly smaller confinement region. Quantifier order must be chosen strong move, **every** legal defending reply, and recursively a bounded continuation; a cooperative route does not suffice.
3. Supply a well-founded phase/tempo measure, with a proof of strict decrease across each completed phase and finite completion inside a phase. A separating wall or chasing the king's file alone does not establish termination. Handle corners and file edges, lateral reversals, waiting moves, rook en prise, any axis changes, and stalemate. Prove each chosen move legal and every required reply set nonempty. Do not assume a full kernel reflection/rotation theorem unless it is proved for the relevant positions and flags.
4. Use EC-T0008 finite-rank forcing rules and EC-T0010 safety/liveness as appropriate. Distinguish local progress, liveness and `ForceMate`; none can be substituted for another. General arbitrary strong-turn legal KRK arrival still needs a safe setup theorem after re-entry is solved. Attack that next if the re-entry policy closes; keep EC-C011 PROPOSED until all required cases are proved.

## Proof, audit and Lean deliverables

Write a standalone paper argument and a same-agent adversarial audit before formalisation. Register a new candidate only for an exact new statement (EC-C014 onward). Check counterexamples locally with disclosed fixed examples or small diagnostics; computational evidence is supplementary, never the general proof. Frozen `Safety.lean`, `CheckProgress.lean`, all earlier frozen modules and manifests are immutable. Put new definitions/lemmas in new files; add new main declarations to `formal/AxiomCheck.lean` and the aggregate imports.

For completed mathematics, formalise in pinned core Lean, incrementally build changed modules and importers, scan for forbidden proof escapes, inspect exact statements and axiom sets, and run relevant Python checks. Gate F promotion requires a fresh GitHub checkout at a published exact proof-source commit, no .lake, with retained new successful build and axiom logs. Do not rerun unrelated clean-checkout theorem certifications. Standard allowed axioms are subsets of propext, Classical.choice and Quot.sound. Do not change verification or checksum requirements to make a failure pass.

If the general policy resists, sustain the attempt, preserve useful proved image bounds or narrower lemmas, identify the precise mathematical gap and attempted policies/counterexamples, and install a remedial next prompt. Do not claim a blocked proof completed, weaken quantifiers silently, or fill the session with redundant definitions. A new valid prerequisite is progress but does not close EC-C011.

## Closeout and publication

Write `sessions/S028_KRK_REENTRY.md`, update the session ledger, candidates and current status documents to match observed results, and install a full next-session prompt with the remaining obligation. Include its full text in the closeout. Distinguish proved, formally checked, supplementary computations and open claims; cite exact source commit, actual test counts, logs and axiom findings. No frozen-theorem ledger change before a later Gate Z session. Commit, push the session branch, merge into main and push main without force; report observed remote publication separately from unobserved hosted CI.

## Cloud tool activation

Use the existing isolated checkout; do not create a worktree unless requested. In each Lean shell set `ELAN_HOME=/workspace/.tools/elan` and prepend `$ELAN_HOME/bin` to PATH. Work in `formal/` for Lake and at the repository root for `python3 scripts/validate_ledger.py` and `python3 -m unittest discover -s tests -v`. Reuse valid incremental .lake outputs. This cloud host ran the unmodified official Lean binaries without the older executable-path shim; use a shim only if the documented path-discovery failure actually occurs, retaining its explicit trust boundary.
