# S031 — Freeze the verified KRK forcing development

Date: 2026-10-19. Base main: `07ff6c0c459562870a6468b383872e8882385421`. Initial `git fetch --all --prune` found main current and no unmerged remote session branches. Work used the existing checkout on `session/s031-freeze-krk`. Publication is authorised by AGENTS.md and the installed S031 prompt. This session changes no Lean proof, game definition, existing frozen manifest or earlier ledger row.

## Result and exact ledger effect

Eight new coherent bundles are FROZEN, bringing the ledger from 11 to **19 bundles**, not nineteen solved material classes. Sixty-two public declarations are partitioned exactly once, together with every constituent module, helper and shared new definition. The entire verified S028–S030 development is retained unchanged at the published anchors below.

| Bundle | Candidate | Scope |
|---|---|---|
| [EC-T0012](../theorems/frozen/EC-T0012/v1.md) | EC-C014 | Exact all-replies image of the opposed-kings checking phase |
| [EC-T0013](../theorems/frozen/EC-T0013/v1.md) | EC-C015 | Bounded upper-band rook-rank advance with immediate rescue |
| [EC-T0014](../theorems/frozen/EC-T0014/v1.md) | EC-C016 | Two-file opposed-kings checking action and upper-edge forced mate |
| [EC-T0015](../theorems/frozen/EC-T0015/v1.md) | EC-C017 | Finite lower-band pursuit conditional on explicit winning exits |
| [EC-T0016](../theorems/frozen/EC-T0016/v1.md) | EC-C018 | Unconditional clock-free forcing from every separated rank wall |
| [EC-T0017](../theorems/frozen/EC-T0017/v1.md) | EC-C019 | Exact ordinary KRK move interface and weak-turn capture safety |
| [EC-T0018](../theorems/frozen/EC-T0018/v1.md) | EC-C020 | Restricted alternating forcing transport and all-axis wall applications |
| [EC-T0019](../theorems/frozen/EC-T0019/v1.md) | EC-C021 and EC-C011 | Arbitrary safe KRK setup and complete clock-free forcing classification |

The conditional pursuit result retains LowerExitWins. The separated-wall theorem has only exact strong-turn Matches and strict rank separation; no exit or safety assumption remains. Transport requires a castling-free source and permits arbitrary target flags; it is one-way forcing transport and does not preserve a claimed optimal distance.

The strong flagship has exactly IsKRK, strong turn and some incoming Legal move; the geometric strengthening uses no weak check instead. The weak classification is actual mate OR nonempty replies with NO legal KK capture; the safe-rook equivalent is also included. Both colours, arbitrary flags, every setup and every legal defending reply are covered. Stalemate, any optional capture, protected-entry nonemptiness, former chase cycles and unsafe setup controls remain explicit. No continuation gap remains within the stated flagships.

S031 reviewed the final papers and retained same-agent paper/Lean audits against exact source statements; no correction was necessary. Classical geometry/strategy is reproved, with no novelty or external-independent-review claim. The full frozen-source boundary is each complete module, including private helpers, not just a list of representative names. Every manifest records transitive project-module hashes; shared modules are referenced across bundles without duplicate theorem rows. Previous source/audit/evidence records remain immutable.

## Actual verification

| Source | Exact proof-source commit | Fresh build | Axiom/statement runner | New public declarations | Gate Z verified UTC |
|---|---|---|---|---|---|
| S028 | `cb5d3bb713257d7cac8e3c1f9d82d8e77b746d6c` | 34 jobs, exit 0 | 212 reports, exit 0 | 15 | `2026-10-19T12:55:24Z` |
| S029 | `3ead1d587f4ff5e129f73666bd466f5eac764223` | 41 jobs, exit 0 | 235 reports, exit 0 | 23 | `2026-10-19T13:03:01Z` |
| S030 | `4acc3e8638a916f329788d4c2b5f0db6f2c9bf67` | 51 jobs, exit 0 | 259 reports, exit 0 | 24 | `2026-10-19T12:47:55Z` |

All three fresh clones came from GitHub, had no formal/.lake before building, and used the exact published SHA. These runs are new Gate Z evidence, not relabelled Gate F output. Complete logs, counts, official toolchain identity, hashes, preconditions and scans are in [VERIFICATION-S031](../theorems/frozen/VERIFICATION-S031/README.md). Axiom subsets: S028 189 standard-three, 10 propext/Quot.sound, 8 propext, 5 axiom-free; S029 204/18/8/5; S030 228/18/8/5. No sorryAx, native reduction or extra axiom. All new declarations have exact statement and axiom results; outputs match their Gate F anchors byte for byte.

Official unmodified Lean 4.35.0, release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, core only, no host shim or dependencies. Zero forbidden tokens across all 22 new modules. The initial concurrent S029 build was killed with exit 137 at the 8 GiB memory limit (cgroup oom_kill=1). The initial S028 build was deliberately stopped (Lean exit 143) to release memory as the remaining pair approached that limit. Both failed/interrupted logs are retained; S030 completed alone, followed by NEW clean-clone S028 and S029 retries run sequentially. Only successful runs count in the table; no successful Lean build was repeated. Full per-module and successful wall timings are retained.

Existing ledger-validator tests: **6 passed**. Structural ledger validation: **19 valid FROZEN rows**. Preservation validation confirms all prior Lean sources, frozen artifacts, papers/audits and Gate F evidence unchanged and the original ledger bytes retained as a prefix. Crosschecks cover all 62 declarations exactly once, matching source hashes, statement/axiom coverage, local manifest links, stable progress rows and the full installed prompt. No existing Python/Lean source changed; unrelated historical diagnostic tests were not rerun. No engine, tablebase or enumeration supplies a theorem. Hosted CI **unobserved**; local success and publishing are not a hosted-CI claim.

## Scope and next obligation

Mathematical coverage is unchanged from S030: this is the separate Gate Z freeze. ForceMate is the existing clock-free finite-rank game. No halfmove/repetition history, numerical DTM/DTZ, full FIDE WDL, seven-piece parity or initial-position result follows. The next session is a short mathematical specification of the rule and distance layer, with one precise bridge obligation; it must not edit frozen game definitions or begin a large unplanned theorem.

## Repeatable progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing classification frozen | FIDE rule/distance parity |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S031 froze eight verified KRK forcing bundles (19 total); mathematical coverage is unchanged, and FIDE rule/distance parity remains open.

## Publication record

The proof-source SHAs above are immutable and precede these manifest/ledger records. The session's publication commit carries this closeout; its own hash is not embedded circularly. The authorised closeout sequence is push session branch, fast-forward main, push main, then compare remote SHA. The final owner reply reports the observed remote result. Verification scripts and full artifacts are committed with the session; temporary GitHub clones are not repository content.

## Full installed S032 prompt

```markdown
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
```
