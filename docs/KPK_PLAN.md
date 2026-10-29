# KPK proof plan

The owner selected KPK as the next class after frozen KQK (EC-T0050).
The owner subsequently authorised continuous execution. The
[partial proof](../proofs/KPK_WDL50.md) records the exact arguments and
remaining gaps. Work through obligations without intermediate freezes
or administrative closeouts; KPK is not yet complete.

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

## Foundation order

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
separate administrative closeouts are needed.

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

### Final theorem contract

Use the pawn owner as the **strong side** and the lone king as the
**weak side**, independently of whose turn it is. State WDL labels from
the side-to-move perspective; also expose the strong-side result so that
changing turns cannot silently reverse a label. The following are
specifications to prove, not definitions of an already known criterion.

For a root `s` in the exact domain, seek explicit geometric predicates
`Win50(s)` and `Live(s)`, with:

- `Win50(s)` iff the strong side has a policy forcing mate against every
  legal opposing policy under the fresh-root rules, with proved bounds
  on each reversible phase.
- Outside `Win50`, a weak-side holding policy prevents a strong-side
  win. Separately prove that the strong side can avoid losing throughout
  the domain; the two holding statements together establish draw.
- `Live(s)` iff some legal continuation reaches mate, with `Dead(s)` its
  complement in the kernel's sense. A possible-mate witness does not
  establish `Win50`, and holding does not establish deadness.

Match the charter's five-valued WDL50 terminology explicitly. If a
no-50-move-limit win can become a draw under the limit, identify its
cursed-win/blessed-loss labels; otherwise prove their absence for this
class. A three-valued win/draw partition alone does not justify claiming
that these two labels are absent. Use only the auxiliary no-limit
comparison needed for those labels; do not expand into incoming-clock
or arbitrary-history classification.

The final criterion must be a finite, readable combination of coordinate,
distance, turn and geometric-region conditions. A recursive minimax
definition, a generic decidability theorem, or an unresolved predicate
such as "can force promotion" is not the requested closed criterion.

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

Build the partition in this order, revising candidate boundaries when a
proof or local counterexample requires it:

1. **Terminal and exit regions:** mate/stalemate, legal pawn capture,
   and each promotion successor. Separate an available capture from a
   capture forced against every strong-side choice.
2. **Immediate promotion geometry:** establish which legal promotion
   choices yield a win, a hold or a terminal draw, with both kings and
   the next player explicit. This supplies the induction boundary.
3. **King-and-pawn coordination:** define candidate support/key-square
   regions and prove entry, preservation and progress. Handle a king
   blocking the pawn's file and the cost of clearing that file.
4. **Defensive geometry:** define candidate blockade and promotion-corner
   holding regions; account for opposition, tempo, the initial double
   step and edge files. Prove a legal response exists whenever the
   position is nonterminal and the proposed invariant requires one.
5. **Approach regions:** prove entry into a classified region using
   distance inequalities and a decreasing measure. A pawn-race distance
   comparison must account for occupancy, attacked squares and turn.
6. **Coverage:** prove the regions cover every admissible root and give
   compatible outcomes on overlaps. Remove every residual open region
   before claiming class completion.

These are proof tasks, not asserted classical criteria. Ordinary and rook
pawns may require different boundary lemmas. Do not assume that a named
key-square rule covers arbitrary locally legal roots, or that promotion
is the only way the pawn side can mate.

### Clock and repetition budget

Use pawn advancement plus a king-phase potential, or another proved
general measure, to force irreversible progress and prevent cycles.
Charge quiet plies between resets, then compose the promotion budget.
Total mate length need not be below 100 if justified pawn moves reset
the clock; resets cannot be assumed without a strategy guaranteeing them.
Prove each required clock interval and preserve all replies and claims.
Restrict history reasoning to prefixes generated from fresh KPK roots;
arbitrary incoming-history classification remains outside scope.

Separate two termination obligations: a well-founded geometric measure
for progress, and an explicit bound on quiet plies before the next reset
or mate. A decreasing measure alone need not supply a sufficiently small
clock bound. A finite bound alone need not exclude an earlier repetition
claim. Prove both for the strategy actually used, including weak replies.
Count in plies and check the exact threshold and mate precedence in the
kernel; do not substitute an informal "50 moves" calculation.

## Implementation order and acceptance criteria

The names below are proposed new modules, subject to the contract audit.
Keep the mathematical argument in `proofs/KPK_WDL50.md` when execution
begins; this plan does not install an unproved theorem as a proof source.

| Stage | Proposed modules under `Rules/KPK/` | Required result before use downstream |
|---|---|---|
| Domain and moves | `Material.lean`, `Moves.lean` | Exact root predicate; sound and complete successor partition; legality, flags and material closure for every branch. |
| Transport | `Symmetry.lean` | File reflection and colour/rank reversal preserve the required rules and outcome semantics; no unsupported pawn symmetry. |
| Exit composition | `Promotion.lean` | All four promotion choices and capture into KK are covered; frozen-result premises and generated-history bridges are proved. |
| Geometric classification | `Geometry.lean`, `Winning.lean`, `Holding.lean` | Explicit regions, legal policies, universal reply arguments, progress and holding invariants. |
| Budgets and semantics | `Bounds.lean`, `FreshOutcome.lean` | Sufficient quiet-phase bounds, repetition avoidance, independent policy transport and complete WDL50/dead-live equivalences. |

Domain and move closure come first. Symmetry and exit composition then
support the geometric proofs. Bounds must be developed alongside winning
lemmas so an unusable unbounded strategy is discovered early. Assemble
the final outcome only after coverage and the semantic bridges hold.

If an existing theorem needs stronger root premises, prove a new bridge
or use its lower-level strategy theorem with verified premises. Do not
weaken the KPK domain to fit reuse. If a geometric candidate fails,
record the precise obstruction in the mathematical source and repair the
region or strategy; adding isolated evaluated positions is not a route
to closure. No fixed numerical budget is promised before its proof.

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
Completed local proofs do not imply class completion; retain explicit
coverage gaps until the complete classification and budgets are proved.
