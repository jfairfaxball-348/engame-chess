# NEXT SESSION — S018 (remedial S017): close the EC-C008 gaps — K+R vs K with the strong side to move is never dead (Gate L)

**Owner instruction:** Execute this S018 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C008 is `PROPOSED`. Nothing here is a proved result.

## Overarching objective (owner, 2026-10-18)
**Proof-based tablebase equivalence:** know, by general theorems formalised in Lean and never by lookup, what an endgame tablebase knows. See `docs/CHARTER.md` and the coverage table in `docs/ROADMAP.md`. EC-C008 completes layer L1 (dead/live) for K+R vs K.

## Context
- Frozen: EC-T0001–EC-T0006. EC-T0006 says that a forced rook capture or a stalemate makes the position dead.
- S017 partial proof: [proofs/EC-C008_KRK_LIVE.md](proofs/EC-C008_KRK_LIVE.md), audit [audits/EC-C008_KRK_LIVE.md](audits/EC-C008_KRK_LIVE.md). Already proved there:
  - the reduction (a) ⇒ (b);
  - normalisation by reflections;
  - **Lemma M** (mate pattern);
  - **Lemma E** (escort, parity, mate);
  - **Lemma W** (walk to `T = S − (0,2)` inside `F`).
- Simulator `scripts/krk_route.py` (about 7 minutes; `tests/test_krk_route.py` samples it). The route reaches mate from all 175,168 strong-to-move states, but the Lemma W hypothesis fails after P1 in 10,752 states.
- Local Lean (elan default `leanprover/lean4:v4.34.1`) when needed.
- Push as `jfairfaxball-348`: the repo-local Git Credential Manager config, with `GCM_INTERACTIVE=never`.
- The working copy is CRLF (`core.autocrlf=true`): hash committed blobs, not working files.

## Objective
Close **G-P1** (rook relocation) and **G-P2** (the lone king ends P1 in `T`'s component of `F`), so that EC-C008 passes Gate L.

## Required work
1. **Repair the route** so that the Lemma W hypothesis always holds after P1. Options:
   - choose the rook's home side (rank 8, files a–c or f–h) by the lone king's file;
   - walk the lone king across before the rook closes the file;
   - add a short pre-phase.

   Make the invariant a hard check in the simulator. Reach 0 failures, with every move verified.
2. **Hand proof of the relocation lemma.** Classify the rook's position relative to the zone and the kings:
   - already home;
   - on rank 8;
   - on files f–h;
   - low-left;
   - behind its own king.

   For each class, show that the chosen route is legal, and that after each rook move the lone king has a non-capturing legal move (or is mated). Treat the lone king's edge and corner cases explicitly: count its neighbours, and those covered by at most two rook lines and by the strong king. The simulator is only for finding counterexamples while designing; per-class counts are supplementary evidence.
3. **Hostile audit** update. EC-C008 → `LOCAL_VERIFIED` only if no gap remains; otherwise state the residual gap precisely.
4. If Gate L passes, record the planned Lean decomposition: each phase as a move schema with a kernel legality lemma, and no per-position certificates (charter: no lookup).

## Closeout
- `sessions/S018_KRK_LIVE_GAPS.md` and a `sessions/SESSION_LEDGER.md` row, recording:
  - changes;
  - proved / tested / conjectured;
  - checks actually run;
  - base and result SHAs;
  - status;
  - ledger effect (none).
- Install the next prompt in full. If Gate L passes, S019 = Lean formalisation of EC-C008 over the kernel. Otherwise, a further remedial session.
- Commit, push, merge to `main`.
