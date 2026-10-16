# Mathematical foundations (model specification, not yet formal proof)

The **chess laws** and our **mathematical abstraction** are different layers. First specify legal game states and transitions, then deduce consequences. Working normative reference: FIDE Laws of Chess effective 1 January 2023, https://handbook.fide.com/chapter/E012023, especially Articles 1.4–1.5, 2.1, 3.8–3.10 and 5.2.2. Record any later version change explicitly.

## Board and metric
Define `F = {0,1,2,3,4,5,6,7}`; squares `S = F × F`. For `p=(x,y)` and `q=(u,v)`, let

`d∞(p,q) = max(|x-u|, |y-v|)`  (Chebyshev distance).

A king attacks a distinct square `q` precisely when `d∞(p,q)=1`. This includes horizontal, vertical and diagonal neighbours, truncated automatically by the board boundary. It is not a legal *move* merely because it is attacked.

## Two-king core state
A core configuration is `(w,b,t)` with White king at `w∈S`, Black king at `b∈S` and side to move `t∈{W,B}`. Define **KK-admissible** by `d∞(w,b) ≥ 2`. Thus the kings occupy distinct non-adjacent squares; no other pieces exist. This is a local legality condition, **not** a claim that every such triple is reachable from the standard 32-piece starting position.

A *core legal king move* changes exactly the moving king's square by distance one, stays on board, does not land on the other king, and leaves both kings at distance at least two. Then the turn swaps. Define `StepKK(p,q)` by these conditions. A rule-complete chess game additionally stops at dead positions; for a counterfactual reachability theorem we first study finite paths of the core transition relation **without** applying the dead-position stopping rule.

## Attack, check, mate, death and draw
- `Attacks(c,s,p)`: a piece of colour `c` attacks square `s` in state `p`, defined by its piece-type movement and occupancy rules.
- `InCheck(c,p)`: king of colour `c` is attacked by an opposing piece.
- `Checkmate(c,p)`: `InCheck(c,p)` and colour `c` has no legal move (with correct side-to-move conditions for an actual terminal checkmate).
- `Reachable*(p,q)`: zero or more core legal transitions. No unquantified 'eventually' or assumed opponent cooperation.
- `Dead(p)`: for neither colour does any finite series of legal core moves from `p` reach a position checkmating that colour. The future quantifier is **existential over any legal move choices**; proving dead requires ruling out *every* possible sequence. This is stronger than 'neither side can force checkmate'.
- `RuleDraw(p)`: a state that has arisen in a legal game is immediately drawn under FIDE Article 5.2.2 once `Dead(p)` holds.

A state can be no-force-mate yet not dead (e.g. some larger-material endings). Clock, resignation, agreements and other administrative outcomes are separate rule layers.

## Candidate derivation for K vs K
1. A KK-admissible position has `d∞(w,b)≥2`.
2. Hence neither king attacks the other; neither is in check.
3. Every core legal move preserves the non-adjacent-king condition and the two-king material invariant.
4. By induction over finite paths, every reachable position is again KK-admissible and neither king is in check.
5. Since check is necessary for checkmate, no reachable checkmate exists; `Dead(p)`.
6. If such a configuration arises under the relevant FIDE rules, Article 5.2.2 makes the game an immediate draw.

**Proof obligation:** justify *every* link from the definitions; establish that the path relation and checkmate predicate model the same notion of legal continuation. Only after hostile local verification may these be labelled proved. See [research/KK_DRAFT.md](../research/KK_DRAFT.md).

## Planned extension points
For bishops, knights, rooks and queens, define separate attack relations with obstruction for sliding pieces. Add full position typing, material invariants, side-to-move, piece captures, king safety and terminal states. For pawns, add directional movement, promotions, en passant, move-history fields and time-based drawing rules only as required by specific claims.
