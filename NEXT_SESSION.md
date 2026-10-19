# NEXT SESSION — S026: Prove progress toward forced mate in K+R vs K

**Owner instruction:** Execute S026 when the owner says "run next session" in this repository or pastes/links this prompt. Follow `AGENTS.md`: fetch latest `main`, merge any unmerged session branch, and finish with the session committed, pushed and merged to `main`. Publishing is authorised as part of the session workflow. Make a sustained mathematical proof attempt; do not end after merely adding definitions or restating the target.

## Ambitions and exact target
- Ultimate ambition, unproved: ultra-weakly establish that standard chess has initial-position value draw, under a complete explicit rules model.
- Active milestone: exact outcome characterisations through seven pieces by mathematics and Lean, without tablebase lookup, whole-class enumeration or per-position certificates.
- **EC-C011 remains PROPOSED.** Primary target: for either colour σ, every kernel position q with `IsKRK q σ S R W`, `q.turn = σ`, and a legal arrival `∃ p, Legal p q`, satisfies `ForceMate σ q` in the explicitly clock-free, repetition-free game. Arbitrary castling/en-passant flags remain in scope. `ForceMate` means a uniform finite ply bound covering every defence, not cooperative reachability.
- No full FIDE WDL/50-/75-move/repetition or distance claim follows until the corresponding rules and bounds are proved.

## Read first and reuse
Read `AGENTS.md`, `docs/CHARTER.md`, `docs/PROOF_PROTOCOL.md`, `docs/ROADMAP.md`; the EC-C011 register row; `research/S024_STRATEGY_ATTEMPT.md`; `proofs/EC-C009_FORCING.md`, `proofs/EC-C010_KRK_CONFINEMENT.md`; the S024 paper/Lean audits; and the S025 closeout.

Frozen infrastructure:
- EC-T0006/0007: exact KRK L1 classification; a legal strong-to-move arrival is live. The cooperative route is not an all-defences forcing proof.
- **EC-T0008:** `Rules/ForcingDefinitions.lean`, `Rules/ForceMate.lean`: finite-rank semantics, monotonicity, soundness, terminal/dead-reply rules, `forceMate_choose` and finite-branching `forceMate_defend`.
- **EC-T0009:** `Rules/KRKConfinement.lean`: arbitrary legal reply completeness under rook protection and a separating-rank invariant. With S strictly below R and W above R, every legal lone-king reply stays above and cannot capture the rook.
- Exact source for EC-T0008/0009: `fca2ca88c8391b1d2bd49c3db9f2fa04258a4a87`, Lean `leanprover/lean4:v4.35.0`, core only. Read their immutable manifests and source statements rather than relying on shorthand.
- No frozen proof or definition module may be edited. New lemmas go in new modules, importing the frozen results.

## Required mathematical work
1. **Broaden rook safety.** The immediate-protection invariant is too narrow for an advancing strategy. At a lone-king turn, investigate the precise capture-avoidance condition "rook at distance at least two from the lone king, or protected by the strong king". Prove its kernel meaning against arbitrary legal replies, including capture, flags and initial check. Do not infer non-stalemate, confinement or progress merely from capture safety.
2. **Resolve the recorded advance obstruction.** `protected_rank_raise_unprotected` proves that raising the rook while keeping its king below the old rank loses immediate king protection. A valid strategy must allow a distant rook or reposition the king through a proved finite phase. Repeated application of the protected barrier alone cannot complete the argument.
3. **Construct an advancing phase on paper.** Choose an exact invariant and a natural/lexicographic phase measure. For each declared phase-entry state, give legal strong-side actions such that **every** legal defending reply either reaches actual mate or permits continuation to a strictly smaller measure after finitely many plies. Cover waiting/tempo moves, rook relocation, king approach, checking moves and board-edge cases. State the precise domain of any proved contraction lemma. Do not hide the key progress assertion in an assumed continuation or an unproved finite-case list.
4. **Close setup as well as progress.** Attempt to bring every strong-to-move legal KRK arrival into the advancing invariant safely. A proof from an invariant family is a prerequisite unless setup from arbitrary q is established. Reflections of a selected KRK move model are not automatically symmetries of the entire general kernel; transport must be justified.
5. **Check terminals and quantifiers in every branch.** Stalemate is not a win; the defender rule requires a nonempty legal reply set. Mate of the lone king is a zero-ply win. An optional legal rook capture can draw a live state. Kernel-check or prove representative critical configurations, including both colours, corners, rook en prise, blocked rook rays and the protected-rank stalemate. Model-move soundness alone does not establish completeness for all opponent replies.
6. **Aim to finish the strong-side theorem.** Once setup, finite-phase progress and termination are proved, derive `ForceMate` using EC-T0008. Only then derive the weak-to-move branches: existing checkmate wins immediately; stalemate does not; any legal capture to KK is a holding action; a nonterminal position without such captures reduces through `lone_move_cases` and `forceMate_defend`. Distinguish “not forcing” from a complete WDL draw classification until both players' outcomes are settled.

## Proof pipeline and permitted diagnostics
Write a standalone proof and adversarial audit before formalising any new claim. Classical rook technique is legitimate; make no unsupported novelty claim. Diagnostics may check local cases and find counterexamples, but cannot replace the symbolic proof with class-wide search, retrograde tables or per-position certificates. No tablebases or engine oracles.

Keep EC-C011 `PROPOSED` until every part of its exact statement is proved. If the general theorem remains open, close and audit the strongest genuinely useful general prerequisite and state the exact missing setup/progress/tempo lemma, including its domain and quantifiers. Do not promote a conditional restatement of the flagship as its solution. Continue beyond an initial failed approach when another concrete route is available.

Only after Gate L: formalise locked statements in new modules (for example `Rules/KRKForcing/`), add main declarations to `AxiomCheck.lean`, compile changed modules/importers, inspect axioms and obtain exact-source Gate F evidence. No ledger changes without completed Gate Z.

## Closeout
Run relevant Python checks and `python3 scripts/validate_ledger.py`. Record `sessions/S026_KRK_FORCING_PROGRESS.md` and the session-ledger row; separate proved, formalised, tested, rejected and open findings. Install the next session around the actual remaining mathematical obligation or required formalisation/freeze gate, include its full executable prompt in the closeout, and commit/push/merge to `main`.
