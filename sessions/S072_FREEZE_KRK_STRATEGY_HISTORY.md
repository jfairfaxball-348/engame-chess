# S072 — Freeze KRK strategy and actual-history milestone

2026-10-20. Base main 233ec1e491309a09ce8fd8fb770613d4d6a5df7f; branch
session/s072-freeze-krk-strategy-history. ALL-head fetch, no unmerged prior work,
latest main in existing checkout. Owner authorised consecutive sessions until
asked to stop; KRK only, stop before KQK.

Milestone B: EC-C041 frozen as EC-T0038, complete 11 KRKStrategy modules/9 public
statements; EC-C042 frozen as EC-T0039, complete 4 KRKHistory modules/3 public
statements, at their DIFFERENT OWN exact sources. Key-simple least-rank policy
retains all weak legal replies; actual-history lift uses explicit clock/current/
incoming lower-winning-rank histogram and gives same-budget RAW rule-mate.
Concrete rank-six wall gets 84 plies with clock≤15 and the stated count conditions.
Strong branch chooses one descending move; weak branch includes every executed
and intended legal move, nonempty replies and terminal children.

[EC-T0038 manifest](../theorems/frozen/EC-T0038/v1.md),
[EC-T0039 manifest](../theorems/frozen/EC-T0039/v1.md). Paper-before-Lean and separate
same-agent paper/Lean audits recorded for both; not independent external review.
No engine/tablebase/exhaustive class proof/stored position certificates/novelty.

Observed separate Gate Z:

S070: own source `fe7efa687ae1481db405cf8808d9ad3437906861`, NEW GitHub clone `/workspace/engame-chess/work/s072-s070-gate-z`, .lake absent; 130 jobs exit 0 in 400.775s, complete runner exit 0 at 2026-10-20T18:35:40Z, 320 permitted reports. Whole own Gate F runner/source/transitive inventories equal; 11 complete modules/9 public declarations inspected.

S071: own source `c6e62cc4b2c96061bdb7465eb99f9cc901941b0c`, NEW GitHub clone `/workspace/engame-chess/work/s072-s071-gate-z`, .lake absent; 134 jobs exit 0 in 395.999s, complete runner exit 0 at 2026-10-20T18:42:22Z, 323 permitted reports. Whole own Gate F runner/source/transitive inventories equal; 4 complete modules/3 public declarations inspected.

Full commands/logs/exits/times/UTC, official core Lean4.35.0/executable, clean
HEAD/tree/status and all hashes retained. Exactly two new fresh builds, each
.lake absent; no fresh failure/interruption/retry, no source edits/incremental
builds or dependency/shim/TLS/checksum changes. Hosted CI unobserved. ENTIRE own
Gate F reports and inventories compared, including older S070 aggregate/runner
rather than current main's later additions. [Evidence](../theorems/frozen/VERIFICATION-S072/README.md).

Relevant ledger tests/structure, all-module/hash/exact-statement audit, protected
sources/prior 37 ledger-byte prefix/prior frozen records, full table/full prompt/
links and diff checks passed. Exactly two new ledger rows. No unrelated tests
or diagnostics. This freeze serves the actual direct KRK strategy/history
milestone and returns immediately to numerical coverage, not a generic detour.

A PARTIAL conditional RAW winning family is frozen. No compatible-history witness,
full FIDE correspondence, complete all-history outcomes/holding or exact distance
parity. Failure of a sufficient condition is not draw. EC-C039 remains verified
backlog; no default generic freeze installed. 39 bundles, not 39 solved classes.
S073 targets sharper wall/pursuit bounds and actual clock-coverage payoff.

Publication: all changes committed/pushed branch, merged/pushed main and matching
remote identities checked. Git anchors exact closeout state without circular
own-SHA text. Continue consecutive authorised sessions.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; raw history/rule prerequisites frozen; conditional budget lifting formally verified; 508-ply bound frozen; key-simple strategy and conditional 84-ply RAW wall family frozen | Concrete FIDE integration, complete rule-aware outcomes and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S072 froze the key-simple strategy and conditional actual-history 84-ply RAW wall certificate as EC-T0038/0039; 39 bundles are frozen, while full FIDE outcomes and exact distances remain open.

## Full installed S073 prompt

# NEXT SESSION — S073: Sharper KRK pursuit/wall clock coverage

Owner requests consecutive sessions until asked to stop. KRK only; stop before
KQK. Follow AGENTS/charter/proof protocol. Fetch ALL heads, merge prior unmerged
work, latest main in existing checkout. Commit/push branch, merge/push main,
compare remote identities. Full stable progress table, Syzygy last and delta.

Milestones A/B starting evidence: EC-T0037 global 508-ply clock-free KRK arrival
ceiling and wall 84*(7−R.y); EC-T0038 minimal-rank key-simple all-defence strategy;
EC-T0039 actual-history RAW lifting and conditional 84-ply rank-six wall family.
39 frozen bundles, not classes. Source anchors: EC-C040 3a4a543625673383f66de70a8f847e340d820570,
EC-C041 fe7efa687ae1481db405cf8808d9ad3437906861,
EC-C042 c6e62cc4b2c96061bdb7465eb99f9cc901941b0c.
EC-C039 remains older verified backlog, not a default freeze detour. Full FIDE
correspondence, complete all-history outcomes/holding and exact distances open.

Principal direct task: improve the numerical strategy bound and thereby widen
its concrete RAW clock/history family. Start from actual frozen KRKBound.Pursuit,
LowerBand, Wall, WallCeiling, KRKHistory.Wall and their complete paper/audits.
Use a standalone paper and separate SAME-AGENT adversarial audit BEFORE Lean.
Do not invent a sub100 global maximum or claim optimality from an upper bound.
Every weak legal reply and nonempty witness must remain.

A precise tractable candidate to investigate (NOT a proved result): the current
oriented pursuit cost 8*m+E overpays at m=1. At remaining oriented distance1,
strict offset forces the weak king onto the approached edge; an offset-one
rook tempo can only exit upward or align, so costs at most2 plies. Test whether
induction gives8*m−6+E for m≥1, with local good/wide/offset-one costs 2/6/8.
Wide/good states require m≥2; do not use truncated subtraction without this.
At m=1 the continuing wide branch must be impossible by file bounds. Alignment
still costs the exit budget, not an invented free mating move. Upward exits
and both physical directions retained. If proved, the uniform lower bound is
50+E instead of56+E.

Then audit an explicit wall budget 76*(7−R.y) using inner
76*(n−1)+56+4*(g−1), ready smaller by2. Normalization at EACH gap still costs 2;
king-rank advance adds2; upper rank advance/rescue costs 4. g≤6 gives overhead
at most76, so coefficient76 is a proposal derived from the candidate pursuit
bound. Edge n=1 must use actual named mate and no nonexistent rank-seven wall.
If valid, an admitted rank-six wall with clock+76<100 (clock≤23), currentcount<3
and the unchanged LowerRankHistory certificate gets raw RuleMateWithin at 76,
using EC-T0039's supplied-budget lift. This is a PARTIAL conditional RAW family,
no compatible-history witness/full FIDE or class closure. Do not silently upgrade
the existing frozen 84 theorem or edit its module.

Choose the exact claim only after the paper/audit closes. If this improvement
fails, retain the exact inequality/counterfamily and continue the direct pursuit
cost problem rather than substituting an unrelated generic theorem. A stronger
amortized bound may be researched, but do not assume it or hide waiting/rescue
costs. Do not claim a new global arrival ceiling unless its actual setup/axis
composition is also proved/formalised. The fixed constants in frozen setup
modules cannot simply be renamed to imply 460 or another numeral.

If closed, new one-main-per-theorem modules/shared definitions, add mains/helpers
to AxiomCheck, preserve every frozen source/record. Incremental changed/importer
build and full runner; own published FULL proof-source SHA, then ONE NEW GitHub
clone/.lake absent/full build/full runner, standard-three only; full retained
logs/commands/exits/times/UTC, source/import/executable hashes, clean identity and
working/clean equality. Official core Lean4.35.0, ELAN_HOME=/workspace/.tools/elan,
inherited proxy/CA, no dependency/shim/TLS/checksum changes. Gate Z separate;
no promotion before observed evidence. No oracle/tablebase/exhaustive class proof
or stored per-position certificates. Same-agent audits labelled honestly.

Update candidate/roadmap/README/completion/progress/session ledger and
sessions/S073_KRK_SHARPER_WALL_BOUND.md with actual evidence, exact newly covered
clock/history inputs or unchanged coverage, remaining gap and FULL next prompt.
Commit/push/merge/push, compare remotes, continue authorised sessions until owner
asks to stop. Sharper budgets, history compatibility/FIDE bridges, complete
necessary-and-sufficient outcomes/holding and exact WDL/DTZ all remain separate.
