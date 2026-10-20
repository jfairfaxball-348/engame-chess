# EC-C037 — Lean fidelity review

S062, same-agent audit, not independent external review. Paper and separate
adversarial audit completed before Lean. Definitions and AppendLifting are NEW;
all frozen sources remain byte-identical. Admissible recurses on the actual
indexed Trace, with True at start and exact parent State at snoc.

Main append_and_reply_lifting states the exact requested conjunction. For EVERY
s/m/hm, destructing s makes the append guard definitional (Iff.rfl), preserving
all trace data. The second conjunct extracts actual m/hm from Legal and chooses
append; its admissibility uses the guard's reverse implication and its step and
endpoint witnesses are reflexive. There is no child classifier filter, material
or colour restriction, arbitrary history reconstruction or changed legality.

Terminal children lift, terminal parents cannot append; optional claims may be
declined. Relative raw classifier semantics only, no certified FIDE correspondence
or complete Layer/strategy/distance theorem. No enumeration/oracle/certificates,
full-game diagnostic or novelty claim. Gate F passed.

Own proof source `67850895bf6130a1f193c299597cd7d4ac209485`; NEW GitHub clone `/workspace/engame-chess/work/s062-gate-f`, .lake absent before build. Full 88-job build exit 0 (582.973s); complete AxiomCheck exit 0 at 2026-10-20T14:20:50Z, 284 allowed reports. Exact main inspected, standard-three axioms only; entire working/clean runner output and all formal bytes identical.

Paper and separate adversarial audit completed before Lean, then LOCAL_VERIFIED.
New definitions/main module, additive aggregate imports/runner; frozen sources
untouched. Working build and complete runner passed first attempt. One new GitHub
Gate F clone, no clean-build retry or failure. Full logs, commands/exits/times/UTC,
clean HEAD/tree/status, executable/toolchain identity, source/transitive SHA256
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependency/shim/TLS/checksum changes. Runtime policy observation state unknown,
executor snapshot unrestricted, inherited proxy/CA sufficient. Hosted CI unobserved.
Relevant ledger tests/structure, evidence, preservation, full progress table/prompt,
local-link and diff checks passed. All prior protected files/34 ledger rows
unchanged. No unrelated diagnostics/trivial tests. Gate Z remains separate.
