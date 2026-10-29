# KQK proof plan

Planning review of KRK source at `45c452e`; no KQK theorem is proved here.
KRK remains complete under the [charter target](CHARTER.md#parity-target-hard-boundary-owner-2026-10-29).
KQK implementation awaits owner approval of this plan.

## Target

Cover both colours and turns of every fresh legal K+Q versus K position:
clock zero, no incoming history or castling rights. State local legality
explicitly (distinct pieces, separated kings, and the side that just moved
not left in check); do not require an entire trace from the initial position.

Candidate classification, with `σ` the queen side:

- Strong turn: forced win.
- Weak turn: forced win exactly when already mated, or when the queen is
  safe and a legal reply exists. Safe means
  `2 ≤ dInf queen weakKing ∨ dInf strongKing queen = 1`.
- Otherwise draw: stalemate or a legal queen capture into dead KK.

Prove dead/live separately: an optional queen capture may make a position
drawn while another cooperative continuation still allows mate. These are
KQK proof obligations, not results of this review.

## Transfer map

Paths below are relative to `formal/EndgameChess/Rules/`.

| KRK source | Reuse and required change |
|---|---|
| `KRKLive/Basic`: `play_board_simple`, `legal_of_pseudo`, distance helpers | Import general declarations unchanged. Add exact KQK board/attack interfaces; orthogonal rays reuse rook clearance geometry, diagonal rays need their own clearance statement. |
| `KRKForcing/Safety`, `CaptureSafety`: `krk_safe_reply`, `krk_unprotected_capture` | Distance-or-protection capture arguments carry over almost verbatim, restated for KQK. Surviving weak replies must avoid diagonals too. A captured queen no longer attacks. |
| `KRKForcing/WallForce`, `WallActions`, `CheckProgress`; `KRKBox/Region`, `Phase` | Reuse confinement, king pursuit and box potentials as templates. Queen replies satisfy rook attack exclusions; orthogonal strong moves remain candidates. Every nonmating weak turn needs a new legal-reply witness. Strategies and costs do not transfer automatically. |
| `KRKBox/Definitions`; `KRKCentral/Costs`, `Arrival` | `KRKBoxPhase` is already piece-independent despite its name; import it. `boxExcess` is pure arithmetic. Reuse induction and cost-composition patterns, deriving costs from queen phases. |
| `KRKLive/Main`: `lone_move_cases`, `krk_dead_iff`; `KRKForcing/OutcomeClassification` | Reprove the weak-move partition (KQK or KK), then reuse the classification argument after strong-turn forcing. Derive liveness from forcing where possible instead of porting the long cooperative rook construction. |
| `KRKForcing/StrategyTransport`; `KRKLive/Basic`: `BoardSym` | Named reflections/transposition need diagonal attack/clearance preservation proofs. The abstract interface states rook geometry; queen transport needs an explicit additional guarantee. |
| `KRKCentral/FreshArrival`, `FreshWeak`, `FreshOutcome`; `KRKFresh/FreshLift` | Reuse bounded-forcing-to-clock-zero architecture. These declarations depend on exact KRK predicates, material regions and policy semantics, so cannot be applied directly to KQK. Use fresh roots and decreasing strategy rank; avoid porting incoming-history machinery. |

Extra attacks do not monotonically preserve a win. White Kc6/Qb6 versus
Black Ka8, Black to move, is stalemate: a7, b7 and b8 are covered, while
a8 is not checked. Replacing Qb6 with Rb6 leaves a7 available. This is a
coordinate illustration, not a new Lean result.

## Proof route and generalisation

1. **Interface and safety:** define exact KQK material, queen attacks and
   legal moves; prove weak capture/survival and terminal criteria. Cover
   exposed queens and boundary positions, not just protected setups.
2. **Confinement:** develop one protected orthogonal wall/box strategy
   with an explicit escape square on every nonmating weak turn. Use a
   lexicographic potential (box dimensions, king approach distance,
   bounded preparation phase). Prove all replies preserve the region and
   every cycle decreases the potential. Handle narrow strips and corners
   with general end-phase lemmas. Diagonal setup moves must preserve the
   same safety/reply invariant.
3. **Bound and outcome:** compose phase costs into strong/weak ply bounds
   strictly below 100. Aim to improve KRK's 97/98 plies, but a shorter or
   optimal bound is not a completion gate. No numerical queen bound is
   claimed yet. Connect forcing and capture/stalemate holding to fresh
   WDL50 on both turns and colours.
4. **Verification:** paper/Lean correspondence, focused builds and
   dependants, main declarations in `AxiomCheck.lean`, axiom audit and
   pinned proof sources under the [minimal protocol](PROOF_PROTOCOL.md).
   No computed position tables, engine oracles or exact-distance catalogue.

Add small importing modules for shared line-piece geometry and safety
only where rook and queen instances are concrete. Parameterise allowed
rays, blockers and king-capture safety; require legal-reply existence
explicitly in forcing interfaces. Keep queen escape-square and terminal
lemmas specific. Do not copy the entire KRK tree or edit frozen modules.

## Effort and KPK

Relative effort, not a timetable: interface/capture lemmas small;
setup/confinement with non-stalemate witnesses largest and most uncertain;
cost composition and fresh outcome bridge medium once the strategy exists.
If a rook phase loses every queen reply, repair its invariant or choose a
different phase before expanding into position cases.

KPK can consume KQK at a legal queen-promotion successor. `Board.lean`
already defines pawns and four promotion choices; `RawClock/Definitions.lean`
identifies source-pawn events before promotion. Later KPK work must connect
promotion to the successor theorem and clock reset, consider underpromotion
alternatives (KRK supplies the rook class), and prove pawn advance/capture,
key-square/opposition and holding arguments. Promotion alone does not
classify KPK: stalemate, capture and drawn pawn regions require treatment.

**First obligation after approval:** KQK material/attack interfaces and
queen capture/safe-reply lemmas, followed by the confinement invariant.
KPK proof work remains outside this plan's execution scope.
