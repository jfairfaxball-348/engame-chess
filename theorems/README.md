# Immutable theorem ledger

`LEDGER.csv` records **only completed, FROZEN theorems**, not candidates, proposed proofs, draft Lean projects or tests. The current frozen results are listed below.

Each row must identify one precise theorem, its proof statement, locally audited mathematical proof, exact Lean source and declaration, compiler version, the immutable 40-hex-character Git commit SHA containing the **verified Lean proof**, build/axiom verification timestamp, pinned chess rule edition and a freeze manifest.

Recommended on-disk manifest: `theorems/frozen/EC-T0001/v1.md`. Place supporting logs under that directory or link to an immutable artifact containing them. The manifest is not a substitute for independent code review.

The freeze commit must be **later than** its referenced verified proof commit so it can cite an existing Git SHA; do not attempt a self-referential commit hash. An additional tag may anchor the ledger commit.

Corrections require a new versioned entry and clearly visible supersession note; Git history must preserve the original record. No ledger row or proof file may be rewritten without that provenance. The checker `scripts/validate_ledger.py` checks *format/integrity only*; it is not a mathematical proof checker.

**Current toolchain anchor:** EC-T0001–EC-T0006 also have a `v2.md` that re-anchors the theorem on Lean **v4.35.0** (S020 migration, commit `b114ccd`, no source change; see [MIGRATION-S020](frozen/MIGRATION-S020/README.md)). The `v1.md` records remain valid at their own commits on v4.34.1.

EC-T0007–EC-T0033 were first frozen on v4.35.0 and need no migration manifest.

Current frozen count: **33 bundles**, not thirty-three solved material classes:
- [EC-T0001](frozen/EC-T0001/v1.md): K vs K dead position (frozen S003).
- [EC-T0002](frozen/EC-T0002/v1.md): K+B vs K dead position (frozen S006).
- [EC-T0003](frozen/EC-T0003/v1.md): K vs K dead in the general FIDE rules kernel, for any legal arrival and arisen positions. Strengthens EC-T0001. Frozen S010.
- [EC-T0004](frozen/EC-T0004/v1.md): the same for K+B vs K. Strengthens EC-T0002. Frozen S010.
- [EC-T0005](frozen/EC-T0005/v1.md): K+N vs K dead in the general FIDE rules kernel (either orientation, any legal arrival, arisen positions). Stated over the kernel from the start. Frozen S013.
- [EC-T0006](frozen/EC-T0006/v1.md): a K+R vs K position in which the lone king must take the rook (or is stalemated) is dead; via the material-agnostic lemma "not mate + every successor K vs K ⇒ dead". Frozen S016.
- [EC-T0007](frozen/EC-T0007/v1.md): K+R vs K with the strong side to move after a legal move is live; with the lone king to move, dead iff not mate and every legal move captures the rook. Completes the converse of EC-T0006 and the arisen Art. 5.2.2 characterisation. Frozen S023. L1 only.
- [EC-T0008](frozen/EC-T0008/v1.md): clock-free finite-rank forced-mate reasoning: soundness, terminal/dead-reply rules and finite-branching choosing/defending closure. Frozen S025. Framework prerequisite, not a solved material class.
- [EC-T0009](frozen/EC-T0009/v1.md): protected rook rank confinement through every legal lone-king reply, plus reply completeness and the obstruction to a fixed-king protected rank advance. Frozen S025. No full forcing strategy.

- [EC-T0010](frozen/EC-T0010/v1.md): distant-or-protected rook safety, all-reply rank confinement and the nonempty-reply liveness bridge. Frozen S027.
- [EC-T0011](frozen/EC-T0011/v1.md): four-ply checking contraction with four-file margin and opposed kings, plus edge forced mate. Frozen S027. Subsequent S031 bundles close setup/re-entry and classify clock-free KRK forcing; clocks/repetition and distance remain open.

- [EC-T0012](frozen/EC-T0012/v1.md): Exact all-replies image of the opposed-kings checking phase. Frozen S031 from EC-C014.
- [EC-T0013](frozen/EC-T0013/v1.md): Bounded upper-band rook-rank advance with immediate rescue. Frozen S031 from EC-C015.
- [EC-T0014](frozen/EC-T0014/v1.md): Two-file opposed-kings checking action and upper-edge forced mate. Frozen S031 from EC-C016.
- [EC-T0015](frozen/EC-T0015/v1.md): Finite lower-band pursuit conditional on explicit winning exits. Frozen S031 from EC-C017.
- [EC-T0016](frozen/EC-T0016/v1.md): Unconditional clock-free forcing from every separated rank wall. Frozen S031 from EC-C018.
- [EC-T0017](frozen/EC-T0017/v1.md): Exact ordinary KRK move interface and weak-turn capture safety. Frozen S031 from EC-C019.
- [EC-T0018](frozen/EC-T0018/v1.md): Restricted alternating forcing transport and all-axis wall applications. Frozen S031 from EC-C020.
- [EC-T0019](frozen/EC-T0019/v1.md): Arbitrary safe KRK setup and complete clock-free forcing classification. Frozen S031 from EC-C021 and EC-C011.

[S031 evidence](frozen/VERIFICATION-S031/README.md) records three new fresh exact-source Gate Z builds. The conditional pursuit bundle keeps LowerExitWins; wall/setup flagships have no assumed winning continuation. No clock/repetition or numerical distance claim follows.

- [EC-T0020](frozen/EC-T0020/v1.md): same-budget abstract rule-layer mate/forcing projection; all raw defending replies must lift. Three complete interface/proof modules and two declarations frozen in S034 from EC-C022. No concrete FIDE history or numerical distance result.

[S034 evidence](frozen/VERIFICATION-S034/README.md) retains the new exact-source Gate Z build for EC-T0020. Twenty frozen bundles are not twenty solved material classes.

- [EC-T0021](frozen/EC-T0021/v1.md): concrete initial-rooted raw traces, exact append retention, complete legal-reply lifting and endpoint origin. Four declarations in five modules frozen S037 from EC-C023 at its own S035 proof anchor.
- [EC-T0022](frozen/EC-T0022/v1.md): raw halfmove reset events, castling empty destination, exact append update and global/one-step ply bounds. Six declarations in seven modules frozen S037 from EC-C024; all five trace imports retained unchanged.

[S037 evidence](frozen/VERIFICATION-S037/README.md) records two NEW sequential fresh GitHub builds at the separate published anchors, 59/66 jobs and 265/271 allowed reports. Twenty-two bundles are not twenty-two solved material classes; full FIDE adjudication and numerical distance remain open.

S039: [EC-T0023](frozen/EC-T0023/v1.md) freezes raw multi-step clock growth on actual trace extensions. [Evidence](frozen/VERIFICATION-S039/README.md). Twenty-three bundles; class coverage unchanged.

- [EC-T0024](frozen/EC-T0024/v1.md): conditional raw prefix and every interior prospective-ply clock certificate. Frozen S041 from EC-C026. [Evidence](frozen/VERIFICATION-S041/README.md). No repetition/FIDE claim or numerical KRK conclusion.

- [EC-T0025](frozen/EC-T0025/v1.md): generic fixed-key full raw-history occurrences and exact append count law. Frozen S043 from EC-C027. [Evidence](frozen/VERIFICATION-S043/README.md). Not a FIDE repetition-key/threshold result.

- [EC-T0026](frozen/EC-T0026/v1.md): actual legal-ep availability/effective-target specification. Frozen S045 from EC-C028. [Evidence](frozen/VERIFICATION-S045/README.md). No full FIDE repetition-key/claim result.

- [EC-T0027](frozen/EC-T0027/v1.md): exact kernel LegalEP characterization from actual legality, source pawn, distinct files and empty destination. Frozen S047 from EC-C029. [Evidence](frozen/VERIFICATION-S047/README.md). No normalization/full FIDE key result.

- [EC-T0028](frozen/EC-T0028/v1.md): ordinary raw ep-marker irrelevance, Boolean pseudo-legality and full play; S049 exact-source freeze. [Evidence](frozen/VERIFICATION-S049/README.md).

- [EC-T0029](frozen/EC-T0029/v1.md): effective-ep normalization legality/full-legal-endpoint preservation; both modules frozen S051. [Evidence](frozen/VERIFICATION-S051/README.md).

- [EC-T0030](frozen/EC-T0030/v1.md): normalized-key legal-move/full-legal-endpoint congruence; both modules frozen S053. [Evidence](frozen/VERIFICATION-S053/README.md).

- [EC-T0031](frozen/EC-T0031/v1.md): concrete current normalized-key count after actual append, S055 exact-source freeze. [Evidence](frozen/VERIFICATION-S055/README.md).

- [EC-T0032](frozen/EC-T0032/v1.md): raw current and every intended threshold exclusion, S057 exact-source freeze. [Evidence](frozen/VERIFICATION-S057/README.md).

- [EC-T0033](frozen/EC-T0033/v1.md): exact raw current and every intended threshold exclusion, S059 exact-source freeze. [Evidence](frozen/VERIFICATION-S059/README.md).
