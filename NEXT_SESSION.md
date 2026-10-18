# NEXT SESSION — S020: Lean formalisation of EC-C008 over the rules kernel (Gate F), first part

**Owner instruction:** Execute this S020 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C008 is `LOCAL_VERIFIED` (S019). Do not treat this prompt as evidence that any Lean proof exists.

## Overarching objective (owner, 2026-10-18)
**Proof-based tablebase equivalence:** know, by general theorems formalised in Lean and **never by lookup**, what an endgame tablebase knows (`docs/CHARTER.md`, `docs/ROADMAP.md`). With EC-T0006, EC-C008 settles layer L1 (dead/live) for K+R vs K completely.

## Context
- Proof: [proofs/EC-C008_KRK_LIVE.md](proofs/EC-C008_KRK_LIVE.md); audit [audits/EC-C008_KRK_LIVE.md](audits/EC-C008_KRK_LIVE.md).
- Lemma map:
  - reduction (a) ⇒ (b);
  - normalisation F4;
  - M (mate pattern), E (escort), C (connectivity), W (walk), S (settling);
  - RL-h and RL-f (lone-king replies), P1 (relocation);
  - the theorem.
- This is the largest formalisation so far. **Plan it over several sessions.** This session should build the reusable infrastructure and the end-game half. Do not freeze.
- Local Lean is primary: elan default `leanprover/lean4:v4.34.1`. Run `lake build` and `lake env lean AxiomCheck.lean` locally from `formal/`.
- Push as `jfairfaxball-348` (repo-local Git Credential Manager config, `GCM_INTERACTIVE=never`). The working copy is CRLF; hash committed blobs.
- No `native_decide` and no per-position certificates (charter: no lookup). Small `decide` checks of concrete examples are fine as non-vacuity witnesses.

## Constraints
- Never edit frozen modules: `KK`, `KBK`, and the `Rules/*` modules frozen with EC-T0003–T0006, including `KNK.lean` and `KRK.lean`.
- Put new work in new modules, e.g. `Rules/KRKLive/Basic.lean`, `Rules/KRKLive/Endgame.lean`, `Rules/KRKLive/Relocation.lean`, with one module per main theorem.
- Core Lean only. No `sorry`, `admit`, custom `axiom` or `unsafe`.

## Required work (this session)
1. **Infrastructure.**
   - A characterisation of `Legal` on a `krkBoard` position: rook moves along a clear line and king steps, via `play_nrp`, as in `KNK.lean`.
   - `attacked` and `inCheck` on `krkBoard`, using `pathClear` for the rook.
   - Reflection maps on squares and positions that preserve `Legal`, `inCheck` and `MatedK` (F4). If proving reflection-invariance of the whole kernel is too heavy, state the lemmas for the normalised frame only, and record that choice.
2. **End-game half:**
   - Lemma M;
   - Lemma E (by induction on `j`);
   - Lemma C, as a general lemma on rectangles minus boxes, then instantiated;
   - Lemma W, by induction on a path; the path comes from Lemma C, constructively;
   - Lemma S.
   Each lemma is a schema over arbitrary squares, not an enumeration.
3. Non-vacuity examples by `decide`, e.g. Lemma M's mate.
4. Checks (local, verbatim): `lake build`, AxiomCheck with the new declarations, the forbidden-token grep, and the Python tests and ledger validation.
5. **Lean audit (partial):** `audits/EC-C008_KRK_LIVE_LEAN.md`.
6. EC-C008 stays `LOCAL_VERIFIED` until the full theorem is formalised; record progress precisely.

## Closeout
`sessions/S020_KRK_LIVE_LEAN1.md` and a `sessions/SESSION_LEDGER.md` row: changes, what is formalised, what remains, checks actually run, SHAs, status, ledger effect (none). Install S021 = the rest of the formalisation (RL-h, RL-f, P1, the main theorem `krk_strong_to_move_live` and `krk_dead_iff`), then Gate F. Commit, push, merge to `main`.
