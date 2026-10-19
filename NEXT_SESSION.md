# NEXT SESSION — S032: Specify the KRK rule and distance layer

**Owner instruction:** Execute when the owner says “run next session” or pastes/links this prompt. Follow `AGENTS.md`: fetch all remote branches and latest main, merge earlier unmerged session work first, use the existing checkout, and finish committed, pushed and merged to main without force. Publication is authorised.

**Closing report:** update `docs/SESSION_PROGRESS.md` from actual evidence and reproduce its complete stable table in the closeout and final reply, with full Syzygy parity last and the session delta immediately below.

## Starting point and reading

S031 froze eight additional bundles, EC-T0012–EC-T0019, bringing the ledger to nineteen bundles, not nineteen solved material classes. Read `docs/CHARTER.md`, `docs/PROOF_PROTOCOL.md`, `docs/ROADMAP.md`, `docs/RULES_KERNEL.md`, the S031 closeout and Gate Z evidence, EC-T0008's forcing definitions and EC-T0019's exact classification before designing new semantics.

The clock-free strong theorem covers exact KRK, strong turn and an incoming Legal move; its geometric strengthening assumes no weak check. The weak theorem is actual mate OR nonempty legal replies without any KK capture, equivalently actual mate OR a safe rook and a legal reply. Both colours and arbitrary flags, all setup and defending quantifiers, are covered. Finite rank supplies existence of a finite bound; it does not supply an optimal number or establish that a rule clock cannot expire.

## Principal task: a small mathematical specification, not a large formalisation

Write `research/KRK_RULE_DISTANCE_SPEC.md` with explicit definitions and one tractable next proof obligation. Use the FIDE Laws of Chess effective 2023-01-01 as the named rules source. Read the actual relevant clauses from an authoritative source if available, record the source and retrieval, and identify any unavailable text rather than inventing it. Do not consult any tablebase, engine oracle, derived position evaluations or per-position certificates.

1. Define an extended state over the existing Position containing the reversible halfmove counter and enough history for repetition. Specify legal initial histories and compatibility with board, turn, castling rights and effective en-passant availability; explain when two positions count as the same for repetition. Distinguish arbitrary kernel flags from histories admissible under the new rules.
2. Define transition updates: captures and pawn moves reset the halfmove counter; other moves increment it. KRK has no pawn moves before a material change, and a rook capture transitions to KK. State how history updates and what is retained after a zeroing move. Do not equate zeroing with mate.
3. Give a precise terminal and action precedence: actual checkmate, stalemate, dead position, optional threefold/50-move claims, automatic fivefold/75-move termination, and checkmate on the threshold move. Claims based on an intended legal move must be represented as actions or explicitly scoped out of a named preliminary model. Separate board-rule outcomes from resignation, agreement and time forfeiture. Explain which player's options are quantified in a force/holding definition.
4. Specify clock-free and rule-aware named-winner predicates and their projection relationship. State the hypotheses needed for each proposed implication. Audit whether erasing history alone suffices for the reverse direction, and why a clock-free win need not be a rule-aware win. Give a proof plan for lifting a bounded clock-free strategy with a sufficient remaining clock/history budget; any repetition premise must be explicit. Do not assume a finite rank is already a numerical budget theorem.
5. Choose a first distance target: an exact DTM, an upper bound, or a carefully defined DTZ-style target. Fix plies versus full moves, zero/one counting at mate and capture, min/max quantifiers, terminal and non-winning conventions, rule-clock dependence and the precise target event. Separate custom semantics from any unverified claim of exact Syzygy conventions, including five-valued WDL and cursed/blessed outcomes. List what additional proofs would establish parity.
6. Retain a concise obligation graph and adversarial examples: mate on a draw threshold, stalemate with a protected rook, optional legal rook capture to KK, a reversible chase/repetition, an impending claim by intended move, and identical board positions with different clocks/history. Fixed locally constructed controls may check definitions; enumeration cannot prove a general outcome or distance theorem.

Prefer one narrow proposed bridge lemma with exact hypotheses and a paper derivation. Register EC-C022 only if the specification yields a well-posed claim; otherwise report the unresolved design choice explicitly. Use PROPOSED unless the relevant gates actually pass. No new ledger entry is expected in a design session. Do not modify frozen Position, Legal, MateWithin, ForceMate, theorem modules or manifests; the new layer must live in new files. If a small new formal definition or lemma is warranted, obey one-module-per-theorem and add main declarations to AxiomCheck, with appropriate new verification evidence. Do not begin a large KRK formalisation or switch material classes in this session.

## Deliverables and closeout

Update the roadmap and candidate register only to reflect actual results. Write `sessions/S032_KRK_RULE_DISTANCE_DESIGN.md` with the chosen semantics, unresolved points, exact proposed bridge/distance obligation, proof versus design versus diagnostic status, checks actually run, ledger effect and full progress table. Install a full S033 prompt targeting the smallest concrete proof arising from the design. Preserve the outstanding clock/repetition and distance work; do not mark KRK full FIDE WDL/DTZ or seven-piece parity solved. Commit/push the session branch, merge main, push main and verify the remote SHA. Distinguish observed local results from unobserved hosted CI.

## Cloud activation

`export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`.
Lake commands run from `formal/`, Python from the repository root. Official unmodified Lean 4.35.0, core only, no dependencies or host shim. Keep TLS/signature/checksum verification enabled. Recheck only actual verification obligations; do not repeat historical fresh-clone certifications for a documentation-only design session.
