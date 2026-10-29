# KPK proof plan — installed, not executed

The owner selected KPK as the next class after frozen KQK (EC-T0050).
This request installs the plan only. **Do not execute it until a later
owner request to run the next session.** No KPK proof, computation or Lean
implementation has been started by this installation.

## Target and boundaries

Prove guaranteed WDL50 for every locally legal fresh K+P versus K position,
both colours and turns: clock zero, no prior history, castling rights or
en-passant target at the root.
Specify admissible unpromoted pawn ranks and local legality explicitly;
do not require an initial-position trace. Prove dead/live separately,
actual winning/holding, and bounds sufficient for the 50-move rule.

Exact M4/Mn, DTM and DTZ catalogues are optional, not completion gates.
Do not pursue arbitrary incoming clocks/histories, a broader FIDE bridge,
other material classes, tablebases, engines as proof oracles, exhaustive
retrograde tables or per-position computed certificates, including in Lean.
No numerical KPK bound or complete pawn criterion is asserted here.

## First obligation on the next run

Read live authority and confirm clean/synchronised `main`. Start with a
KPK contract and proof-route audit:

1. Inspect pawn attacks, pushes, double steps, promotions and flag updates
   in `Rules/Board.lean` and `Rules/Moves.lean`.
2. Specify exact material, fresh legality, pawn ranks and the full legal
   successor partition below.
3. Map direct frozen reuse and missing bridges. Draft geometric win/draw
   regions and coverage gaps in the mathematical source. Classical pawn
   rules are candidates until proved over this kernel.
4. Make material/attack and legal-move interfaces, including promotion and
   capture closure, the first formal obligation. Do not substitute a
   sampled family or computed outcome table.

Continue incrementally under `AGENTS.md`; no numbered session folders or
separate administrative closeouts are needed. Execution has not begun.

## Reuse and limits

Paths below are relative to `formal/EndgameChess/Rules/`.

| Source | Reuse / limitation |
|---|---|
| `LoneKing/Material.lean`, `Moves.lean` | Exact K+X material with `.pawn`, king separation and immediate capture safety where applicable. Reprove directional pawn attacks and strong-move completeness. Safe pawn does not imply winning pawn. |
| `Board.lean`, `Moves.lean` | Actual colour direction, starting/last ranks, all four promotion choices and flag updates are the contract. |
| `KQK/FreshOutcome.lean` (EC-T0050) | Full queen-promotion successor outcome, including weak-turn capture/stalemate. Promotion changes the turn; strong-turn queen winning is not the applicable blanket conclusion. |
| `KRKCentral/Arrival.lean`, `KRKForcing/OutcomeClassification.lean` | Rook board forcing/bounds and weak-turn safety criterion. Older RAW-history theorems have different root premises; do not apply them directly to arbitrary fresh KPK roots. |
| `Reach.lean`, `KNK.lean` | Legal capture into dead KK and legal bishop/knight promotion successors. Retain every promotion alternative. |
| `FreshGame/`, `RawClock/Definitions.lean` | Independent policy semantics, normalised keys, actual clock reset and sub100 fresh-root lifting when its premises hold. Extend through new importing modules; existing files are frozen. |

KQK proof source: `c72365a8ba46f59114a2a77d9d38993f6a52df80`;
freeze: `eca65027f4a55149371860653a1aa1de116be300`. Frozen modules,
manifests and ledger rows remain immutable.

## Proof route

### Exact interfaces and irreversible transitions

Account for every legal strong-king move, single/double pawn push with
path clearance, mandatory promotion to queen/rook/bishop/knight, weak
survival/capture into KK, and terminal mate/stalemate/deadness. Explain why
diagonal captures and en-passant branches can or cannot occur in exact
KPK. A double push may set an ep field although no opposing pawn exists;
preserve actual flags until their irrelevance is proved.

KQK's lemma that noncheck implies queen distance at least two is not a
pawn lemma. Pawn attacks are directional. Arbitrary rook/queen
transpositions also fail to preserve pawn movement. Prove pawn-rule
transport before using file reflection or colour/rank reversal.

### Promotion boundary

Prove exact successor material, turn, local legality and clock reset.
Promotion alone is not winning: a queen can be captured or stalemate.
Evaluate all four choices using proved successor results, without assuming
underpromotion irrelevant or necessary in advance.

**Clock reset is not history erasure.** A promotion successor reached from
KPK is not literally a `FreshGame.fresh` state. Prove relevant past keys
cannot cause repetition in the promoted continuation, and transport the
frozen strategy with actual history. Do not invoke a fresh-root theorem
merely because its clock is zero.

### Complete geometric partition

Develop reusable winning and holding regions covering ordinary/rook
pawns, blocked paths, capture threats, both turns, tempo/opposition and
promotion corners. Audit candidate key-square and race principles with
precise quantifiers. Boundary exceptions must follow from geometry, not
a growing catalogue of positions.

Prove winning-region progress against every weak reply and actual holding
for the complement. Keep possible mate, forced mate and draw distinct.
Reconcile all legal positions with the partition; a local family is not
class closure. Keep unresolved regions explicitly open.

### Clock and repetition budget

Use pawn advancement plus a king-phase potential, or another proved
general measure, to force irreversible progress and prevent cycles.
Charge quiet plies between resets, then compose the promotion budget.
Total mate length need not be below 100 if justified pawn moves reset
the clock; resets cannot be assumed without a strategy guaranteeing them.
Prove each required clock interval and preserve all replies and claims.
Restrict history reasoning to prefixes generated from fresh KPK roots;
arbitrary incoming-history classification remains outside scope.

### Outcome and verification

State a closed mathematical WDL50 criterion for every legal root, with
all draw and dead/live branches. Connect it to independent policy
semantics and prove all required numerical bounds. Never infer an outcome
from a failed search, timeout or unproved complementary region.

Use new importing modules under `formal/EndgameChess/Rules/KPK/`; append
main declarations to the axiom runner. Run focused builds when code
changes, with small controls for both colours/turns, double push, blocking,
capture, promotion choice and stalemate. No class enumeration is a proof.
Certify completed source in a clean checkout once, audit axioms, then
freeze under `PROOF_PROTOCOL.md` and update coverage at the milestone.
None of these execution steps has run yet.
