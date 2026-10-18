# NEXT SESSION — S023: Gate Z freeze of EC-C008 (as EC-T0007)

**Owner instruction:** Execute this S023 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C008 is `FORMAL_VERIFIED` (S022). Do not treat this prompt as evidence that it is frozen.

## Overarching objective (owner, 2026-10-18)
**Proof-based tablebase equivalence:** for every ending with fewer than 8 pieces, prove the outcome as a closed mathematical characterisation in Lean, **never by lookup or per-position enumeration** (`docs/CHARTER.md`, `docs/ROADMAP.md`). With EC-T0006, EC-C008 settles layer L1 (dead/live) for K+R vs K.

## Context
- Proof: [proofs/EC-C008_KRK_LIVE.md](proofs/EC-C008_KRK_LIVE.md). Audits: [audits/EC-C008_KRK_LIVE.md](audits/EC-C008_KRK_LIVE.md) (prose) and [audits/EC-C008_KRK_LIVE_LEAN.md](audits/EC-C008_KRK_LIVE_LEAN.md) (Lean, Gate F).
- **Lean:** `formal/EndgameChess/Rules/KRKLive/{Basic,Endgame,Reply,Relocation,Main}.lean`. The proof-source commit is `a8bc161d2a51b92c340697af16a10e874cd9a098` (S022).
- **Main declarations:**
  - `EndgameChess.Rules.krk_strong_to_move_live` (EC-C008(a));
  - `EndgameChess.Rules.krk_dead_iff` (EC-C008(b));
  - corollaries `arisen_krk_strong_live` and `krk_drawn_by_rule_iff`.
- **Toolchain:** `leanprover/lean4:v4.35.0`. `Reply.lean` takes about 2 minutes to build.

## Required work (Gate Z, `docs/PROOF_PROTOCOL.md`)
1. **Clean-checkout verification** at the proof-source commit, from a fresh GitHub clone with no `.lake`:
   - `lake build`;
   - `lake env lean AxiomCheck.lean`;
   - the forbidden-token grep on `Rules/KRKLive/*.lean`.

   Save the logs as `theorems/frozen/EC-T0007/lake_build.log` and `axioms.log`.
2. **Manifest** `theorems/frozen/EC-T0007/v1.md`, in the format of EC-T0006 v1/v2. It records:
   - the statement and scope (both main declarations, verbatim `#check` output);
   - the rule edition, toolchain, proof-source SHA and axiom findings;
   - the trust boundary: the KRK move model is internal and its kernel soundness is proved; A1; the kernel encoding;
   - the relation to EC-T0006 (EC-T0007 completes its converse; `krk_dead_iff` uses EC-T0006 for "⇐").
3. **Ledger:** add one `FROZEN` row for EC-T0007 to `theorems/LEDGER.csv`, citing the proof-source commit (not the manifest's own commit). Run `python3 scripts/validate_ledger.py`.
4. **Status updates:**
   - `research/CANDIDATES.md` (EC-C008 → frozen as EC-T0007);
   - `theorems/README.md`, `README.md`, `docs/ROADMAP.md` (K+R vs K layer L1 frozen), `formal/README.md`.
5. The Python tests (`python3 -m unittest discover -s tests`).
6. **Propose the next research rung** in the closeout. For example, L2 for K+R vs K (the strong side *forces* mate whenever not dead, a ∀-strategy with a descent measure), or K+Q vs K L1.

## Constraints
- Do not edit any Lean module. A defect found at Gate Z blocks the freeze: record it, and install a remedial session instead.
- No tablebases or engine oracles.

## Closeout
- Write `sessions/S023_FREEZE_EC-T0007.md` and a `sessions/SESSION_LEDGER.md` row.
- Install S024 according to the owner's roadmap.
- Commit, push, merge to `main`.
