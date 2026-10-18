# NEXT SESSION — S019 (remedial): prove the rook-relocation lemma G-P1, closing EC-C008 (Gate L)

**Owner instruction:** Execute this S019 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C008 is `PROPOSED`. Nothing here is a proved result.

## Overarching objective (owner, 2026-10-18)
**Proof-based tablebase equivalence:** know, by general theorems formalised in Lean and never by lookup, what an endgame tablebase knows (`docs/CHARTER.md`, `docs/ROADMAP.md`). EC-C008 completes layer L1 (dead/live) for K+R vs K.

## Context
- Frozen: EC-T0001–EC-T0006.
- [proofs/EC-C008_KRK_LIVE.md](proofs/EC-C008_KRK_LIVE.md), route v2 (S018), proves everything after P1: the reduction (a) ⇒ (b), normalisation, and Lemmas M, E, C, W and S. **EC-C008 therefore reduces to one lemma (G-P1).**
- **G-P1 (to prove).** Normalise so that `S = (sx, sy)` has `sx ≤ 3` and `sy ≥ 2`. In every legal strong-to-move state, one of these routes works:
  - direct: one move, if the rook is on rank 8 or the h-file;
  - HV: `(rx,ry) → (h,ry) → h8`;
  - VH: `(rx,ry) → (rx,8) → h8`;
  - detour: `(rx,y₀) → (h,y₀) → h8`, with `y₀` = rank 1, or rank 2 if the rook is on rank 1.

  "Works" means that every rook move is legal and that after each rook move the lone king has a non-capturing legal move (or is mated). The lone king's reply is any such move.
- Simulator `scripts/krk_route.py`: the route mates in all 175,168 states. Usage counts:
  - rook already on h8: 2,752;
  - direct: 36,900;
  - HV: 130,856;
  - VH: 3,438;
  - detour: 1,222;
  - P1 mates by itself in 298 states.
- Useful facts:
  - since `sx ≤ 3`, no square on files f–h is adjacent to `S`;
  - only kings block rook lines;
  - `L` is never in check when the strong side is to move.
- Local Lean (elan default `leanprover/lean4:v4.34.1`). Push as `jfairfaxball-348` (repo-local Git Credential Manager config, `GCM_INTERACTIVE=never`). The working copy is CRLF; hash committed blobs.

## Objective
A hand proof of G-P1, then EC-C008 → `LOCAL_VERIFIED` if no gap remains.

## Required work
1. **Reply lemma.** After a rook move to `ρ`, characterise when the lone king lacks a non-capturing legal move. Its neighbours are covered by at most the rook's rank and file (with x-ray through `L`) and by `N1[S]`; also count edges and corners. Derive a short list of "cramped" patterns. Use the fact that files f–h are never adjacent to `S`. Many rook destinations (h-file, rank 8) attack only lines far from a lone king that sits in files a–e.
2. **Route lemma by class of rook position:**
   - (i) on h8;
   - (ii) on rank 8 or the h-file;
   - (iii) generic: HV path clear and no cramped pattern;
   - (iv) HV blocked or cramped, VH works;
   - (v) both fail: the detour, in which the rook is on rank 8 behind `S` (a shielding case).

   For each class, prove legality and the existence of a reply. Use the simulator only to find counterexamples to intermediate claims, and to report class counts.
3. Update `proofs/EC-C008_KRK_LIVE.md` and the hostile audit. If no gap remains, set EC-C008 to `LOCAL_VERIFIED`. Record the planned Lean decomposition: move schemas with kernel legality lemmas and no per-position certificates (charter: no lookup). If a gap remains, state it precisely.

## Closeout
`sessions/S019_KRK_RELOCATION.md` and a `sessions/SESSION_LEDGER.md` row: changes; proved / tested / conjectured; checks actually run; base and result SHAs; status; ledger effect (none). Install the next prompt in full: if Gate L passes, S020 = Lean formalisation of EC-C008 over the kernel; otherwise a further remedial session. Commit, push, merge to `main`.
