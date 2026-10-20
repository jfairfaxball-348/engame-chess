# NEXT SESSION — S049: Freeze ordinary ep-marker irrelevance

Owner resumed consecutive sessions on 2026-10-20: continue through session
closeouts until told to stop. Follow AGENTS.md and docs/PROOF_PROTOCOL.md.
Explicitly fetch ALL remote heads, merge prior unmerged work, start latest main
in existing checkout. Publication authorised: commit/push branch, merge/push
main, compare remote SHAs, never force main. Reproduce FULL stable progress
table, Syzygy last, followed immediately by one-sentence session delta.

## Starting point and task

S048 formally verified EC-C030, ordinary_ep_irrelevance, at OWN proof-source
c4c900036dcffd209d6c08f27e2323637852c940. Read actual S048 summary/logs,
proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md and both audits; complete OrdinaryEP
module and its unchanged frozen imports; charter/protocol/roadmap/candidates,
S048 closeout, S032 specification. Twenty-seven bundles frozen before this freeze.

Principal task: separate exact-source Gate Z for EC-C030. Audit exact paper/Lean
fidelity and all raw ep uses: guard excludes source-Pawn/distinct-files/empty-dst
shape; no actual legality premise. Marker replacement preserves Boolean isPseudo
and FULL play, including output ep recomputation, castling, promotions and board
function. Review absent/wrong-colour/nonpawn/king/castling, same-file/occupied
pawn cases, both colours, source=destination, arbitrary markers. ¬LegalEP alone
is insufficient for total raw play equality. Same-agent review must not be
called independent external audit. No new source edits, enumeration or oracle.

Run ONE NEW GitHub clone at OWN FULL proof-source SHA above, ensure formal/.lake
absent before full lake build and COMPLETE AxiomCheck. Official core Lean4.35.0,
standard-three axiom subsets only; inspect exact main, compare entire S048 report,
all formal bytes, full source/transitive SHA256, clean HEAD/tree/status, retain
commands/exits/times/UTC/toolchain identity. ONE fresh build at a time. Hosted CI
unobserved unless actually inspected. Only observed success permits immutable
EC-T0028/v1.md and exactly one appended ledger row. Preserve all prior source,
papers/audits/evidence/manifests and 27 rows byte-for-byte; no source/incremental
build needed when source unchanged. Run relevant ledger tests/structure and
preservation/evidence/document checks; no unrelated diagnostics/trivial tests.

## Closeout and continuation

Update candidate/roadmap/README/session ledger/progress; write
sessions/S049_FREEZE_ORDINARY_EP_IRRELEVANCE.md with actual complete evidence and
FULL installed S050 prompt. Commit/push/merge/push and verify remote identities.
Continue S050 under standing owner authorisation unless stopped.

Prepare S050 for effectiveEP normalization preservation, only after a complete
standalone paper/audit: define normalizeEP q={q with ep:=effectiveEP q} in a NEW
shared definitions module and one NEW main theorem module. Intended statement
for all raw q,m: isLegal(normalizeEP q)m=isLegal q m AND
(isLegal q m=true → play(normalizeEP q)m=play q m).
Available EP means normalized q=q. Without legal EP, ordinary moves use EC-C030
plus inCheck unchanged; EP-shaped moves cannot be legal in original q by frozen
legalEP_iff_shape. Normalized marker none makes pawnMoveOK false on that shape:
dx≠0 removes straight moves, empty dst ordinary capture, none marker EP. Prove
both illegality directions without assuming compatible histories or raw play
equality for illegal EP shapes. No full FIDE repetition key/rights correspondence,
claims/adjudication, strategy lifting, numerical KRK, WDL/DTZ or solved class claim.

Use cloud runtime guidance/status/network policy, inherited proxy/CA and existing
ELAN_HOME=/workspace/.tools/elan. Lake in formal/, Python at root. No toolchain,
dependency, TLS/checksum changes absent an actual blocker.
