# NEXT SESSION — S011: K+N vs K is a dead position (EC-C003), Gate L, stated over the rules kernel

**Owner instruction:** Execute this S011 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C003 is `PROPOSED`. Do not treat this prompt as evidence that it is solved.

## Context
Four theorems are frozen:
- **EC-T0001**: K vs K, bespoke model.
- **EC-T0002**: K+B vs K, bespoke model.
- **EC-T0003**: K vs K over the general FIDE rules kernel `formal/EndgameChess/Rules/`, for any legal arrival.
- **EC-T0004**: K+B vs K over the same kernel, for any legal arrival.

The kernel is the single FIDE→Lean bridge (`docs/RULES_KERNEL.md`; human review still open). New endgame results are **stated directly over the kernel**. There will be no new bespoke move model. This removes the agreement step (K2) that EC-T0001/0002 needed.

## Objective
Write a complete, hostilely audited **paper proof** (Gate L) that every K+N vs K position, in either orientation, produced by any legal move (from any material), and hence every arisen one, is dead under the kernel's rules. Plan its Lean statement over the kernel, but **do not write Lean in this session** (that is S012). The ledger is unchanged.

## Non-negotiable scope
- FIDE 2023 as encoded in the kernel. Knight moves come from `Rules.knightGeom` (Art. 3.6).
- No tablebases, no engine oracles.
- **Checks are possible**: the knight can check the lone king. Mate must be excluded by escape-square geometry, not by the absence of check.
- **Correct geometric facts, to be checked against the diagnostic before use:**
  - A knight always moves to, and attacks, squares of the **opposite colour** to its own square.
  - So if the knight checks the lone king `k`, then `k`'s **diagonal** neighbours (which have the same colour as `k`) are never attacked by the knight. Its **orthogonal** neighbours may be.
  - Two squares a knight attacks are never orthogonally adjacent, but they **can be diagonally adjacent** (from a1 the knight attacks b3 and c2).
  - A checking knight is never adjacent to the king it checks (offset (1,2)), so it cannot be captured immediately.
  - **The colour argument alone is not enough.** A corner king has exactly one diagonal neighbour, and the strong king can cover it without being adjacent to the lone king (e.g. lone K a8, strong K b6). The proof must also handle the orthogonal neighbours in corners and on edges: which of them can the knight and the king jointly cover?
  - Find the right lemma, and prove it with an explicit, complete case analysis. Use symmetry of the board (reflections and rotations preserve both knight and king geometry) to reduce the cases, and justify each symmetry used.

## Required work
1. **Model in prose over the kernel.**
   - Define `IsKNK q σ sk ns wk`, analogous to `Rules.IsKBK`.
   - The class closed under legal moves is K+N vs K together with K vs K. If the weak king captures the knight, the position is K vs K and **EC-T0003** applies (`dead_of_legal_into_KK`).
   - Use the kernel's flag irrelevance (`Rules.deadK_normFlags_iff`; no rooks and no pawns are present).
2. **Lemmas.**
   - N0: the last move is legal, so the side not to move is not in check, so the kings are not adjacent.
   - N1: knight colour flip and attack geometry.
   - **N2 (key): a checked lone king always has a legal move**, by complete case analysis with symmetry.
   - N3: closure of the class under legal moves, including the capture branch.
   - N4: induction over move sequences, giving no reachable checkmate, so dead.
   - Corollary: by `Rules.Rule5_2_2` the position is drawn immediately.
3. **Diagnostic.** `scripts/knk_diagnostic.py` plus a unit test, written independently (enumerate knight offsets directly):
   - all placements, both orientations, both sides to move;
   - counts of checks, checkmates (expected 0) and stalemates (report them);
   - closure into K+N vs K ∪ K vs K;
   - a check of every geometric claim used in N1/N2.
   - **Mutation test:** e.g. give the piece an extra move, such as a king step. Mates must then appear, and the diagnostic must detect them.
4. **Proof and audit.**
   - `proofs/EC-C003_KNK.md`, self-contained.
   - `audits/EC-C003_KNK.md`, hostile, covering: corners, edges, both orientations, both sides to move, knight on the edge, capture branch, zero-length path, double check (impossible: why?), and every symmetry used.
5. **Status.**
   - EC-C003 → `LOCAL_VERIFIED` only if no gap remains; otherwise stay `PROPOSED` and state the gap.
   - Record the **planned Lean statement** for S012: `Rules.dead_of_legal_into_KNK` and `Rules.arisen_KNK_dead` in a new module `Rules/KNK.lean`, proved directly over the kernel, reusing `Flags`, `Reach` and `AgreeKK`.

## Closeout
- Write `sessions/S011_KNK_PROOF.md` and a `sessions/SESSION_LEDGER.md` row, recording:
  - the changes;
  - what is proved, what is tested and what is conjectured, as separate lists;
  - the checks actually run;
  - base and result SHAs;
  - candidate status;
  - the ledger effect (none).
- Install the next prompt in full. If Gate L passes, S012 = the Lean formalisation of EC-C003 over the kernel (Gate F). Otherwise, a remedial S011.
- Then commit, push and merge to `main`.
