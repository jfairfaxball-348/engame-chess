# NEXT SESSION — S050: Effective en-passant normalization preservation

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Explicitly fetch ALL remote heads, merge unmerged prior work,
start latest main in existing checkout. Publication authorised: commit/push
session branch, merge/push main, compare remote SHAs; never force main. Full
stable progress table in closeout/report, Syzygy last, immediate session delta.

## Starting point and reading

S049 froze ordinary ep-marker irrelevance EC-C030 as EC-T0028, OWN source
c4c900036dcffd209d6c08f27e2323637852c940. Read its manifest/evidence, complete
OrdinaryEP source/paper/audits, EC-T0026/27 definitions/specification/characterization,
Rules/Moves all ep uses and inCheck, S048/49 closeouts, roadmap/candidates and
research/KRK_RULE_DISTANCE_SPEC.md. Twenty-eight frozen bundles, not classes.

## Principal task

Before Lean, write exact standalone paper and separate adversarial audit. Register
EC-C031 only after complete local argument, LOCAL_VERIFIED. Add NEW shared
NormalizationDefinitions module defining noncomputable normalizeEP q :=
{q with ep := effectiveEP q}, then ONE NEW main theorem module Normalization:
for EVERY raw q,m,
 isLegal (normalizeEP q) m = isLegal q m ∧
 (isLegal q m = true → play (normalizeEP q) m = play q m).
First equality Boolean; second FULL Position equality for actual legal moves.
No valid-history, material, terminal, colour or promotion restriction; no new
seed/clock/count/game filter. Frozen sources untouched; aggregates additive only.

Complete argument to audit:
* If ∃move,LegalEP q move, effectiveEP q=q.ep, hence normalizeEP q=q.
* Otherwise effectiveEP q=none. Outside source-Pawn/distinct-file/empty-dst raw
  shape, frozen ordinary_ep_irrelevance gives identical isPseudo and full play;
  same turn then gives identical inCheck test and isLegal.
* Inside shape, original move cannot be legal by frozen legalEP_iff_shape and
  no legal EP witness. Normalized source pawn/turn/board unchanged; dx≠0 removes
  straight single/double, empty dst removes ordinary capture, marker none removes
  EP branch, so normalized isPseudo/isLegal false too. Prove both Booleans false.
  Actual-legal implication impossible in this branch. Do NOT claim raw play
  equal for illegal EP-shaped moves (pinned/raw marker removal control).

Audit absent/wrong-colour/nonpawn/king/castling, same-file/occupied pawn moves,
promotion fields, source=destination, both colours, malformed markers, pseudo-only
EP exposing check. Keep actual original Move and self-check semantics. Symbolic
branch proof, no enumeration/tablebase/engine/stored certificates. Same-agent
review transparently named; no claim of independently staffed audit or concrete
full promotion/castling/threshold game run. Classical kernel reasoning, no novelty.

## Verification and closeout

Incrementally build changed modules/importers; full working AxiomCheck. Publish
proof source BEFORE ONE NEW GitHub Gate F clone at FULL exact SHA; no .lake
before full build then COMPLETE runner. Inspect exact main and only standard-three
axiom subsets; retain all logs/commands/exits/times/UTC/toolchain identity,
source/transitive SHA256, clean HEAD/tree/status; compare full working/clean
output and formal bytes. Official core Lean4.35.0, no dependencies/shim. Gate Z
separate; no frozen manifest/ledger row in S050. Preserve prior frozen sources,
papers/audits/evidence/ledger byte-for-byte. Relevant ledger/evidence/preservation/
full table/prompt/local-link/diff checks; no unrelated diagnostics/trivial tests.
If gap appears, record honestly rather than weakening statement or claiming success.

Update candidate/roadmap/README/session ledger/progress; write
sessions/S050_EFFECTIVE_EP_NORMALIZATION.md with actual evidence and FULL installed
S051 prompt (consider separate exact-source freeze before composing key).
Commit/push/merge/push and compare remote identities. Hosted CI unobserved unless
actually inspected. Continue next session under owner authorisation unless stopped.

No full FIDE repetition-key/Article9.2.3/rights-history correspondence, lawful-history
invariants, claim/automatic draw/mate precedence adjudication, strategy lifting,
numerical KRK bound, holding/outcome, WDL/DTZ/Syzygy or initial-position result.
This preservation lemma is one component; altered raw q need not have compatible
initial-rooted history. No adverse legal reply may be pruned.

Use available cloud runtime guidance/status/network policy; inherited proxy/CA,
ELAN_HOME=/workspace/.tools/elan and official toolchain. Lake in formal/, Python
at root; ONE fresh build at a time, TLS/checksums unchanged.
