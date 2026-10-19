# S032 — adversarial design review for the rule/distance layer

Same-agent review; not independent external review and not a Gate F certificate.
Target document: `research/KRK_RULE_DISTANCE_SPEC.md`. EC-C022 stays PROPOSED;
the generic interface and its recurrence still need a Gate L/fidelity review
and formal definitions. No concrete FIDE layer is declared verified.

| Attempted falsification | Resolution / outstanding boundary |
|---|---|
| h=99 but no current fifty-move claim | ClaimIntended quantifies a legal prospective move; its correct claim ends the current game without executing it. |
| Give the defender a turn after mate at h=150 | Classify the child as mate first; no claim action or further board move exists there. Winner may decline its current claim before the mating move. |
| Assert a universal fivefold/checkmate override from 9.6.1 | Do not infer an extra clause; on admissible traces, an earlier occurrence of the mated key would already have ended the game. This exclusion is a future history invariant. |
| Drop draw-ending legal replies from the extended move relation | Explicit completeness condition (B) is an interface hypothesis, not a new logical axiom. All raw Legal replies must lift, including children that draw. Otherwise erasure can produce a false forced win. |
| Clock-aware holding erases to holding | Rejected: a draw claim can be the only defence against a clock-free mate. Only the named-mate projection is proposed. |
| Reuse arbitrary flags as lawful history | Excluded from concrete admissibility; full traces derive rights/ep. Generic bridge does not certify any particular history implementation. |
| Count a raw ep flag or lose blocked castling rights in repetition | Key uses legal effective ep and retains rights. FIDE correspondence and the pinned-ep lemma remain future proofs. |
| Reset history when h resets, or reset h when rights are lost | Keep full trace; only pawn moves/captures reset h. Compression needs a separate theorem. |
| Rook capture satisfies a custom zeroing objective and hence wins | Rejected: KK is immediate dead draw. The selected target is opponent mate; any future zeroing distance must preserve a winning outcome. |
| Finite clock-free rank implies enough budget | Rejected: no numerical rank below 100 is supplied. Sufficient lifting needs both h+n<100 and a full-history repetition certificate covering every defending announced move. |
| Protected rook implies a nonempty reply set | Frozen stalemate control retained. Both recurrences require nonempty defending board replies. |
| A small board/counter example proves full-history reachability | Explicitly rejected. Local suffix controls are conditional on compatible prefixes unless such a prefix is supplied. No new diagnostic or reachability proof is claimed. |

Paper induction for C022 was checked branch by branch: base goal is exactly
frozen MateGoal; strong existential uses soundness; weak nonemptiness uses
soundness, universal raw-reply coverage uses completeness; both ongoing
branches use nondeadness; the same n decreases once per actual board move.
The defender's no-claim guard may be discarded only in this projection
direction. No finiteness or KRK strategy premise is needed for that implication.

No unjustified converse, determinacy result, numerical KRK bound, complete
rule-aware outcome or exact Syzygy convention has been proved. The target is
one small parametric theorem followed by a separately audited concrete
instantiation. Existing game definitions, proofs, manifests and ledger remain
unchanged. A source clause table is a normative bridge to be reviewed; Lean
will not prove that the text of the Laws says what the model encodes.
