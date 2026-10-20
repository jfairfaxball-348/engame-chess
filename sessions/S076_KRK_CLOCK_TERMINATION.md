# S076 — Universal admitted RAW KRK clock-bounded termination

2026-10-20. Base main `2c1359d4bde4a5facafad9cbc6427ecbd821bb0a`;
branch `session/s076-krk-clock-termination`. ALL-head fetch, no prior unmerged work,
latest main in existing checkout. Owner's latest steering: finish this session,
then STOP. S077 saved/paused and not started; no automatic continuation.

EC-C045 FORMAL_VERIFIED, Gate Z pending. Universal admitted RAW KRK termination formally verified: every ongoing root of clock h has at most150−h board plies, terminal roots0; both turns/colours/all flags/every legal move including castling and terminal rook capture.
Region is exact KRK OR terminal; typed BoardStep forces parent ongoing from
child admission. Every step preserves region and spends one fuel. Every finite
path satisfies P(end)+length≤P(root); maximal endpoint terminal; some terminal
continuation exists by well-founded induction. An arbitrary truncated prefix
need not be terminal. Mate at clock150 retains mate-first terminal status; this
is not a draw label. Claims are zero-board-ply stopping actions, no passes.

[Standalone paper](../proofs/EC-C045_KRK_CLOCK_TERMINATION.md),
[separate same-agent paper audit](../audits/EC-C045_KRK_CLOCK_TERMINATION_PAPER.md),
[Lean fidelity audit](../audits/EC-C045_KRK_CLOCK_TERMINATION_LEAN.md).
Paper/audit preceded Lean. Four-part direct prerequisite admission: all-history
KRK outcome horizon blocked, frozen noRights strong completeness/upper-only clock
bound insufficient, smallest all-flag material/quiet-or-dead step, immediate exit
to typed potential/termination. Castling splits just two symbolic rule schemas;
weak king coordinates remain universal. No generic detour or material-count oracle.

Observed Gate F: OWN published source `e7508e103b3515dc138ed21e2ea5d3adda255add`; ONE NEW GitHub clone, .lake absent before full build. 168-job build exit0 in440.64s; COMPLETE AxiomCheck exit0 at2026-10-20T19:46:24Z,354 permitted reports.
All ten public statements/eleven complete modules and their transitive imports
checked. Full working/clean report/formal bytes identical; complete hashes,
clean source identity/toolchain/commands/exits/times/UTC retained. No fresh clone
failure/retry or dependency/shim/TLS/checksum changes; hosted CI unobserved.
[Evidence](evidence/S076/README.md). Same-agent audits, not independent review.

Actual checks: changed/importer incremental build and complete runner, new own-
source Gate F, six relevant ledger tests, 41-row structural ledger validation,
831-file older source/config/frozen-record byte preservation, forbidden tokens,
full stable table/immediate delta/FULL paused prompt/local links/diff. Authoring
failures and quick-validation whitespace repair retained. No oracle, tablebase,
class enumeration, per-position certificate or unrelated diagnostic runs.

Universal termination is a new direct all-branch RAW obligation discharged,
not complete all-history holding/outcomes, full FIDE key/rights/claim/adjudication
correspondence or optimal distance/WDL/DTZ. Frozen442/443 bounds and conditional73
RAW family unchanged; failure of a sufficient histogram proves no draw.41 frozen
bundles unchanged. Future own-source freeze and genuine holding/outcome attack
remain saved obligations requiring an explicit new owner request. Stop before KQK.

Publication: source/closeout committed/pushed on session branch, fast-forward
merged/pushed main and matching remote identities checked. Git records final
state without a circular self-SHA. STOP after S076 as requested.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing, conditional 73-ply RAW family and 442/443 bounds frozen; universal RAW termination formally verified | Concrete FIDE integration, complete rule-aware outcomes/holding and exact distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S076 formally verified universal admitted RAW KRK termination within150−h board plies, covering every legal move/all flags; 41 bundles remain frozen, full FIDE/outcomes/holding/exact distances remain open. Sessions now paused by owner request.

## Full saved future prompt (PAUSED; not started)

# NEXT SESSION — S077: Freeze universal admitted RAW KRK termination (PAUSED)

Owner's latest instruction, 2026-10-20: finish S076, then STOP. This is a saved
future prompt only. DO NOT start S077 or any later session automatically. Wait
for an explicit new request to resume. KRK remains the research priority; do
not start KQK. Follow AGENTS/charter/protocol on any later authorised resumption.
Fetch ALL remote heads, merge prior unmerged work, latest main in existing
checkout; commit/push branch, merge/push main, compare remote identities. Full
stable progress table, Syzygy last, immediate mathematical delta.

Principal future task: separate own-source Gate Z for EC-C045, the all-move
termination milestone directly needed for KRK all-history holding/outcomes.
41 frozen bundles before session; next free ID EC-T0042. EC-C039 remains backlog,
not the default freeze detour. Read S076 closeout/evidence, standalone exact paper,
separate SAME-AGENT paper and Lean audits, all complete new sources and imports.
OWN published proof-source: e7508e103b3515dc138ed21e2ea5d3adda255add.

Exact C045 domain: EXISTING RawHistoryLayer.State, full initial-rooted actual
legal trace with strict-prefix admission. Either strong colour, BOTH turns,
ALL flags and EVERY legal board move, including unchosen/bad strong moves and
actual strong castling. No winning strategy, safety, noRights, clock/current
count or incoming repetition histogram assumption. Legal KRK move is quiet
retained KRK OR dead KK from weak rook capture. Actual castling is proved from
two symbolic canCastle schemas, sole home rook, empty king/crossing destinations;
weak king coordinates remain universally quantified, not board enumeration.

Region = exact KRK OR not ongoing. P=if ongoing then150−storedClock else0.
Every typed admitted BoardStep forces parent ongoing from CHILD admission and
append iff, preserves region and satisfies P(child)+1≤P(parent). Ongoing children
increment stored clock exactly1; terminal/reset children have fuel0. Path uses
forward typed cons/refl, not unguarded RawTrace.Extends. All finite paths have
P(end)+length≤P(root); ongoing exact KRK cap150−h, terminal root length0.
No successor iff not ongoing; maximal endpoints terminal; a terminal admitted
continuation exists by strong induction on P using full nonempty legal replies.
Mate at clock150 stays terminal mate-first, never automatically labelled draw.
Truncated prefixes need not be terminal. Claims stop with zero board plies.

All TEN public main declarations in AxiomCheck, ELEVEN complete KRKTermination
modules including shared Definitions. Own Gate F complete runner has354 permitted
reports, full library168 jobs; confirm actual S076 observations rather than
calling expected counts success. New source is additive; all older frozen source
and records unchanged. Gate Z must use ONE NEW GitHub clone at the FULL OWN SHA,
.lake absent before full build and COMPLETE matching own AxiomCheck. Compare
ENTIRE OWN Gate F source/transitive inventories and full working/clean output,
not later current main aggregates. Record full logs/commands/exits/times/UTC,
source/import/executable hashes, clean HEAD/tree/status and all exact statements.
Official core Lean4.35.0, ELAN_HOME=/workspace/.tools/elan, inherited proxy/CA;
no dependencies/shims/TLS/checksum changes. No Lean edits/incremental substitutes.
Retain failures/retries; hosted CI unobserved unless actually inspected.

Only after observed Gate Z success create complete immutable EC-T0042 record,
all helpers/shared definitions/source boundaries, exact types/import hashes,
trust/scope/provenance. Exactly1 ledger row; prior41 rows/frozen records remain
byte-identical. Relevant ledger tests/structure, preservation/evidence/module/
type/hash checks, links/full table/full prompt/diff. Update candidate/roadmap/
README/completion/theorem index/progress/session ledger and full S077 closeout.
Publish branch, merge/push main, compare identities. Whether any further session
is authorised must follow the owner's latest instruction; the current instruction
is to STOP after S076, and this saved prompt grants no automatic continuation.

C045 is universal RAW termination, NOT complete rule-aware KRK outcome/holding,
full FIDE key/rights/claim/adjudication correspondence or exact WDL/DTZ. Frozen
442/443 clock-free bounds exceed100. Partial73 RAW family still requires explicit
clock/current/incoming conditions; failure of those conditions proves no draw.
After any later authorised freeze, return directly to a genuine all-history
RAW holding/outcome attack using the universal horizon: actual mate/draw terminal
semantics, EVERY legal and current/intended claim action, both turns and all
history counts. Prove strategy/holding soundness and necessary/sufficient content;
merely renaming RuleMateWithin, enumerating positions, or substituting a generic
finite-game slogan is not class closure. If a prerequisite is needed identify
exact blocked KRK step, insufficiency of current results, smallest missing
statement/payoff and immediate exit back to that proof. Paper and separate
adversarial audit BEFORE new Lean. No tablebases, engine oracle, exhaustive class
proof, per-position certificate or novelty/completion claim. Stop before KQK.
