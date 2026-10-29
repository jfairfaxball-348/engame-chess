# Endgame Chess — mathematics first

A proof-first research programme in mathematical chess endgames.

**Operational objective:** prove, via general mathematics formalised in Lean 4, the guaranteed win/draw/loss outcome (under the 50-move rule) of every position that Syzygy tables provide, ultimately through seven pieces — **without consulting, replaying or deriving outcomes from tablebases**.

**Long-range aspiration (unproved):** an *ultra-weak* solution of chess: establish that standard chess from its initial position is theoretically drawn. This is a hoped-for mathematical discovery, not a claimed result, and not a request to build a playing oracle.

## How research runs now
Research can proceed continuously in local laptop sessions. **There are no mandatory numbered sessions, per-session documents, closeouts, progress-chart updates or separate freeze sessions.** Commit meaningful source work; prove and formalise results; verify and freeze them when ready. Preserve the source and Lean integrity of every certified theorem. See [AGENTS.md](AGENTS.md) for the short working rules and [minimal proof standard](docs/PROOF_PROTOCOL.md) for the only required theorem certification steps.

There is one active research target and a concrete direct obligation. Supporting lemmas are useful only insofar as they move that obligation; don't equate many frozen lemmas with a complete material class.

## Where the work lives
- [Current obligation / resume point](NEXT_SESSION.md) — compact live note, not a session gate
- [Class roadmap and actual coverage](docs/ROADMAP.md)
- [KRK status and remaining work](docs/KRK_COMPLETION.md)
- [Scientific charter and rule boundaries](docs/CHARTER.md) · [formal definitions](docs/FOUNDATIONS.md) · [methods](docs/METHODS.md)
- [Frozen theorem ledger](theorems/LEDGER.csv) · [immutable proof manifests](theorems/frozen/) · [Lean library](formal/) · [proofs](proofs/) · [audits](audits/)
- [Research candidates](research/CANDIDATES.md)

The `sessions/` tree contains historic work and verification evidence. It is **not** an active reporting workflow, and no new session files are expected.

## Current scientific position
**49 frozen theorem bundles** through EC-T0049; K vs K, K+B vs K and K+N vs K have proven draw/dead-position results. **KRK is complete** under the outcome target: every position's result is proved and frozen (exact distance-to-mate only through 13/14 plies, which is optional).

After KRK, the next proposed classes are KQK and KPK; moving material classes requires owner direction. Neither complete seven-piece parity nor a proof that the initial chess position is drawn exists in this project.
