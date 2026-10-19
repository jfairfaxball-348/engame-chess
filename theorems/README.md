# Immutable theorem ledger

`LEDGER.csv` records **only completed, FROZEN theorems**, not candidates, proposed proofs, draft Lean projects or tests. The current frozen results are listed below.

Each row must identify one precise theorem, its proof statement, locally audited mathematical proof, exact Lean source and declaration, compiler version, the immutable 40-hex-character Git commit SHA containing the **verified Lean proof**, build/axiom verification timestamp, pinned chess rule edition and a freeze manifest.

Recommended on-disk manifest: `theorems/frozen/EC-T0001/v1.md`. Place supporting logs under that directory or link to an immutable artifact containing them. The manifest is not a substitute for independent code review.

The freeze commit must be **later than** its referenced verified proof commit so it can cite an existing Git SHA; do not attempt a self-referential commit hash. An additional tag may anchor the ledger commit.

Corrections require a new versioned entry and clearly visible supersession note; Git history must preserve the original record. No ledger row or proof file may be rewritten without that provenance. The checker `scripts/validate_ledger.py` checks *format/integrity only*; it is not a mathematical proof checker.

**Current toolchain anchor:** EC-T0001–EC-T0006 also have a `v2.md` that re-anchors the theorem on Lean **v4.35.0** (S020 migration, commit `b114ccd`, no source change; see [MIGRATION-S020](frozen/MIGRATION-S020/README.md)). The `v1.md` records remain valid at their own commits on v4.34.1.

EC-T0007–EC-T0019 were first frozen on v4.35.0 and need no migration manifest.

Current frozen count: **19 bundles**, not nineteen solved material classes:
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
