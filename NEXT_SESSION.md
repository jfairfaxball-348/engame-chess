# NEXT SESSION — S021: Lean formalisation of EC-C008 over the rules kernel (Gate F), first part

**Owner instruction:** Execute this S021 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C008 is `LOCAL_VERIFIED` (S019). Do not treat this prompt as evidence that any Lean proof exists.

## Overarching objective (owner, 2026-10-18)
**Proof-based tablebase equivalence:** for every ending with fewer than 8 pieces, prove the outcome as a closed mathematical characterisation in Lean, **never by lookup or per-position enumeration** (`docs/CHARTER.md`, `docs/ROADMAP.md`). Together with EC-T0006, EC-C008 settles layer L1 (dead/live) for K+R vs K.

## Context
- Proof: [proofs/EC-C008_KRK_LIVE.md](proofs/EC-C008_KRK_LIVE.md). Audit: [audits/EC-C008_KRK_LIVE.md](audits/EC-C008_KRK_LIVE.md).
- Lemma map: the reduction (a) ⇒ (b), normalisation F4, the end-game lemmas M, E, C, W and S, the reply and relocation lemmas RL-h, RL-f and P1, and the main theorem.
- This is the largest formalisation so far. **Plan it over several sessions.** In this session, build the reusable infrastructure and the end-game half. Do not freeze.
- **Toolchain:** `leanprover/lean4:v4.35.0` (S020 migration; Palomar minimum `v4.35.0-rc2`). The elan default is v4.35.0. Run `lake build` and `lake env lean AxiomCheck.lean` locally from `formal/`.
- The Palomar module-system port is not done. The owner asked only for the version, so do not start it unasked. New modules may be written module-ready, but should match the existing non-module style unless the owner decides otherwise.
- Push as `jfairfaxball-348` (repo-local Git Credential Manager config, `GCM_INTERACTIVE=never`). The working copy is CRLF, so hash committed blobs.
- No `native_decide`, no custom axioms, no per-position certificates. Small `decide` checks are fine for concrete non-vacuity witnesses and for bounded local lemmas.

## Constraints
- Never edit frozen modules: `KK`, `KBK`, and the `Rules/*` modules frozen with EC-T0003–T0006, including `KNK.lean` and `KRK.lean`.
- New work goes in new modules, e.g. `Rules/KRKLive/Basic.lean`, `Rules/KRKLive/Endgame.lean` and `Rules/KRKLive/Relocation.lean`, with one module per main theorem.
- Core Lean only. No `sorry`, `admit`, custom `axiom` or `unsafe`.

## Required work (this session)
1. **Infrastructure:**
   - characterise `Legal` on a `krkBoard` position: rook moves along a clear line and king steps, via `play_nrp`, as in `KNK.lean`;
   - characterise `attacked`/`inCheck` on `krkBoard`, using `pathClear` for the rook;
   - reflection maps on squares and positions that preserve `Legal`, `inCheck` and `MatedK` (F4). If proving reflection-invariance of the whole kernel is too heavy, state the lemmas for the normalised frame only, and record that choice.
2. **End-game half:**
   - Lemma M;
   - Lemma E, by induction on `j`;
   - Lemma C, as a general lemma on rectangles minus boxes, then instantiated;
   - Lemma W, by induction on a path, with the path taken constructively from Lemma C;
   - Lemma S.

   State each one as a schema over arbitrary squares, not as an enumeration.
3. **Non-vacuity** examples by `decide`, e.g. Lemma M's mate.
4. **Checks**, run locally and recorded verbatim:
   - `lake build`;
   - `AxiomCheck`, with the new declarations added;
   - the forbidden-token grep;
   - the Python tests and the ledger validation.
5. **Partial Lean audit:** `audits/EC-C008_KRK_LIVE_LEAN.md`.
6. EC-C008 stays `LOCAL_VERIFIED` until the full theorem is formalised. Record progress precisely.

## Closeout
- Write `sessions/S021_KRK_LIVE_LEAN1.md` and a `sessions/SESSION_LEDGER.md` row covering: changes; what is formalised and what remains; the checks actually run; SHAs; status; ledger effect (none).
- Install S022: the rest of the formalisation, then Gate F. That means RL-h, RL-f, P1, the main theorem `krk_strong_to_move_live` and `krk_dead_iff`.
- Commit, push, merge to `main`.
