# NEXT SESSION — S054: Full normalized-key current occurrence append law

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Fetch ALL remote heads, merge unmerged prior work, latest main,
existing checkout. Commit/push branch, merge/push main, compare remote identities;
never force main. FULL stable progress table, Syzygy last, immediate session delta.

## Starting point and reading

S053 froze EC-C032 as EC-T0030 at OWN proof-source
7ada0bfa5731cae92a965a17d56695b4dbd221ef; 30 frozen bundles, not solved classes.
Read actual S053 manifest/evidence including interrupted-run/retry record;
S052/53 closeouts, EC-C032 paper/audits, KeyDefinitions/KeyCongruence, frozen
normalization/EP modules, RawOccurrences definitions/append and RawTrace append/
definitions; S032 specification, roadmap/candidates/charter/protocol.

## Principal task

Before Lean write exact standalone paper and separate adversarial audit. Register
EC-C033 only after complete local argument. NEW shared OccurrenceDefinitions:
noncomputable occurrences {q}(t:RawTrace.Trace q)(a:Position):Nat :=
by classical; exact RawOccurrences.occurrences key t (key a).
noncomputable currentOccurrences(s:RawTrace.State):Nat :=
occurrences s.trace (RawTrace.erase s).
Use SAME full normalized Position equality/classical DecidableEq locally;
no global executable hash/search/DecidableEq instance. Frozen sources untouched.

ONE NEW main theorem module, every raw state s and actual legal move m/hm:
currentOccurrences (RawTrace.append s m hm) =
 occurrences s.trace (play (RawTrace.erase s) m) + 1.
Full endpoints/actual Move/legality/stored trace retained. Unfold new definitions,
apply frozen generic append_occurrences at queried NEW endpoint key; indicator
is 1 because new key equals itself. ALL prior root/current endpoints retained,
including after pawn/capture clock resets; no truncated list/terminal filter.
No claim currentOccurrences(child)=currentOccurrences(parent)+1: old query is
NEW key. Audit symbolic [A,B,A] then B: new count2, old-current count2, false
old-current-plus-one3. Not a concrete compatible chess history claim.

Audit proof irrelevance of hm if encountered (no synthetic trace/erased-history
replacement), initial/root inclusion, identical/different queried keys, arbitrary
flags/EP, promotions/castling/both colours, no-legal-reply states, every actual
append. Concrete count depends only on chosen full normalized key; its move
congruence does NOT establish full FIDE identity iff or historical-rights validity.
No repetition threshold/claim certificate merely from append law. Same-agent
review transparently named, not independent external audit. Classical bookkeeping,
no novelty/enumeration/engine/tablebase/stored certificates/full-game diagnostic.

## Verification and closeout

One new theorem module plus shared definitions; aggregates additive. Incremental
changed modules/importers and COMPLETE working AxiomCheck. Publish proof source
BEFORE ONE NEW GitHub Gate F clone at FULL exact SHA, .lake absent before full
build then COMPLETE runner; inspect exact main/standard-three subsets, retain
full logs/commands/exits/times/UTC/toolchain/executable, all source/transitive SHA256,
clean HEAD/tree/status; full working/clean report and source equality. Official
core Lean4.35.0, no dependencies/shim. One fresh build at a time. Infrastructure
interruptions recorded honestly and preserved; fresh retry only when justified.
Gate Z separate, no new frozen manifest/ledger row in S054. Preserve all prior
protected source/paper/audit/evidence/manifests and 30 rows. Relevant ledger/
evidence/preservation/full-table/full-prompt/local-link/diff checks only; no
unrelated diagnostics/trivial tests. Record gaps honestly, don't weaken claim.

Update candidate/roadmap/README/session ledger/progress; write
sessions/S054_NORMALIZED_KEY_OCCURRENCES.md with actual evidence and FULL installed
S055 prompt (consider separate own-source freeze). Commit/push/merge/push and
compare remotes; hosted CI unobserved unless inspected. Continue until owner stops.

No full FIDE Article9.2.3/rights-history identity, no-earlier-terminal histories,
claims/automatic draws/mate precedence adjudication, strategy lifting, numerical
KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position result.

Use available runtime guidance/status/network policy, inherited proxy/CA,
ELAN_HOME=/workspace/.tools/elan. Lake in formal/, Python root; official core
Lean4.35.0, TLS/checksums unchanged.
