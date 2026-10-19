# KRK rule and distance specification — S032

**Status: mathematical design, not a new formal result.** Frozen EC-T0019
classifies clock-free KRK forcing. This document chooses an additive history
layer, proposes EC-C022, and selects a finite ply upper bound as the first
distance target. Nineteen frozen bundles and their source bytes remain unchanged.
Classical rules are being specified, not claimed as discoveries.

## 1. Rules source and scope

Authoritative source: FIDE, *Laws of Chess taking effect from 1 January 2023*,
<https://handbook.fide.com/chapter/E012023>, retrieved 2026-10-19 at
13:14:54 UTC (14:14:54 Europe/London). HTML SHA-256:
`c5b1692a0614d4bd93fe9238287b9ab7d1f47320934d5df3be113523906c476f`.
The actual Articles 5 and 9 were read; their text was available. Retrieval and
clause coverage are recorded in `sessions/evidence/S032/fide-source.json`.
The hash agrees with the earlier kernel source retrieval. Clause summaries:

| Articles | Consequence for this layer |
|---|---|
| 5.1.1 | Legal checkmate immediately wins and ends play. |
| 5.2.1–2 | Stalemate and dead position immediately draw. |
| 9.2, 9.2.1–2 | Threefold repetition is claimable by the player to move, either now or by announcing an intended move. |
| 9.2.3–3.2 | Repetition compares placement, turn and move possibilities, including en-passant availability and lost castling rights. |
| 9.3.1–2 | Fifty moves by each player without pawn movement or capture permit a claim, now or based on an intended move. |
| 9.4, 9.5.1–3 | Touching a piece loses the claim right for that move; correct claims end play; incorrect claims have procedural/time consequences. |
| 9.6.1 | Fivefold repetition automatically draws. |
| 9.6.2 | Seventy-five moves by each player without a pawn move or capture automatically draw; checkmate on the last move takes precedence. |

Chosen scope: ideal board decisions **before touching a piece**, with correct
claims available as separate actions. The physical execution provisos of
Articles 4.2–4.7, scoresheet/arbiter mechanics, false-claim penalties, draw offers,
resignation, agreement, thinking clocks and forfeiture are outside this named
model. Thus this is an Article 3/5/9 board-and-correct-claim model, not a claim
to have formalised every tournament procedure. An intended claim is not scoped
out. A fuller procedural game would add turn phases, touch status and arbiter
outcomes; the current state represents the fresh pre-touch decision of each
turn. Invalid claims are not legal actions here.

## 2. Extended state and admissible histories

Keep the frozen `Position`, `Legal`, `play`, `DeadK`, `MateWithin`, and
`ForceMate` unchanged. Proposed state is `s = (q, h, H)`, with:

- q: the existing kernel position, including turn, raw castling rights and ep;
- h: natural-number plies since the last pawn move or capture, initially zero;
- H: the entire finite trace `q0, m0, q1, ..., m(k−1), qk`, including the initial
  and current positions, not just the moves since entering KRK.

q must equal qk. For the full-history model q0 is the standard `initial`, each
move is kernel-legal and qi+1=`play qi mi`, and h is derived by §3. All strict
prefixes must be ongoing under §4: no move may follow an earlier mate,
stalemate, dead position or automatic draw. The trace records no successful
claim, since any such claim already ends play. Claim opportunities may have
been declined. The current endpoint may itself be terminal. This is the
proposed `AdmissibleHistory`, stronger than raw `ReachK initial q`.

A KRK starting snapshot must carry such a preceding history, or an explicit
compatible-prefix witness. A local board example plus an arbitrary clock and
count vector is only a diagnostic state until that compatibility is proved.
The trace derives castling rights and ep flags rather than granting arbitrary
flags. EC-T0019's arbitrary-flags theorem remains useful by projection, but it
does not assert that every flagged position has an admissible FIDE history.
At lawful KRK snapshots no pawn has a legal ep capture; the model must prove
any stronger claim that raw ep is always none rather than assume it.

### Repetition key

Define `LegalEP(q,m)` to mean that m is a **legal**, actual en-passant capture
by q.turn, using the kernel's pawn/ep transition, not merely a pseudo-legal
capture. Define `effectiveEP(q)` as q.ep if some such move exists, else none.
A pinned pawn unable to make a legal ep capture does not distinguish positions.
Proposed key is:

`K(q) = (piece placement, turn, castling rights, effectiveEP(q))`.

Do not include h, the move number, prior repetition counts, or a bare ep field
which offers no legal capture. Keep castling rights even when castling is
currently blocked: after a king/rook moves, loss of that right is still relevant.
Do not identify positions merely because their *current* legal-move lists agree.
On history-derived rights this key is intended to implement Article 9.2.3;
proof of that correspondence is an outstanding rules-encoding obligation.
Arbitrary malformed flags are not an alternative justification for that claim.

`occ(H,k)` counts position endpoints in H with key k, INCLUDING q0 and qk.
`rep(s)=occ(H,K(q))`. Prior occurrences need not be consecutive and need not
arise by repeating the same move sequence. H itself is authoritative; no
unproved compressed representation is adopted.

## 3. Move updates and zeroing

For every legal actual move m:

- q'=`play q m` and the turn flips as in the kernel;
- `Zero(q,m)` iff the mover is a pawn OR the move actually captures an enemy
  piece, including en passant; promotion is a pawn move;
- h'=0 when Zero, otherwise h'=h+1;
- H'=H with m and q' appended, then repetition is counted against the full H'.

Actual capture can be specified by ordinary destination capture or the legal
en-passant capture event. Equivalence with material-count decrease is a lemma
to prove on admissible traces, not an assumption for corrupted kernel boards.
A king/rook move that merely loses castling rights increments h; loss of
rights is not a fifty-move reset. KRK has no pawn moves: before material change
its king/rook moves increment h. A weak rook capture resets h to zero and
leaves KK; the legal-arrival KK theorem then supplies immediate dead draw.
A zeroing move is not automatically mate, a win, or a successful distance goal.

Keep the full repetition trace even after zeroing. Pruning before a pawn move,
capture, or rights loss requires a separate equivalence proof. In particular,
clock resets and loss of future repetition equivalence are distinct events.

## 4. Terminal precedence and draw-claim actions

Evaluate the endpoint BEFORE offering any further action:

1. Actual legal checkmate: the player opposite q.turn wins.
2. Stalemate or `DeadK q`: draw.
3. rep(s)≥5 or h≥150: automatic draw.
4. Otherwise ongoing: offer moves and the correct claims below.

The dead-position test is the existing clock-free `DeadK`; do not redefine
a clock-expired draw as board deadness merely because play must stop.

One hundred plies means fifty moves by EACH player; 150 means seventy-five by
each. A completed move first creates q', h', H', then endpoint classification
runs. Thus a legal mate on the move taking h from 149 to 150 wins. Article
9.6.2 explicitly supplies that priority. Mate first is also a convenient total
classifier: on an admissible trace, a newly mated repetition key cannot have
appeared earlier, because its earlier occurrence would already have ended
play. No extra priority clause against a feasible simultaneous fivefold mate
is inferred from 9.6.1; that overlap is excluded by admissibility. Deadness and
mate are incompatible; overlapping draw conditions have the same result.

At an ongoing pre-touch decision by c=q.turn, actions are:

- `Play(m)`, for EVERY kernel-legal m, even when its child immediately draws.
- `ClaimNow`, if h≥100 OR rep(s)≥3.
- `ClaimIntended(m)`, if m is kernel-legal and the prospective update has
  h'≥100 OR `occ(H',K(q'))≥3`.

A correct claim immediately draws in the CURRENT state, without executing m
or appending q'. In particular, an intended claim is available at h=99 when
its announced legal move is nonzeroing. At h=99 an announced pawn move/capture
would reset the counter and does not justify a fifty-move claim. An intended
repetition claim can apply even if its move is zeroing, whenever the key test
is satisfied; impossibility on lawful histories, where applicable, needs proof.
The announced move is binding under the Laws; here every admitted claim is
correct and terminal, so no continuation needs a binding-move register. Invalid
claims and their required move/penalty are outside this ideal-action model.

`CanClaim(s)` is the disjunction of ClaimNow and existence of ClaimIntended(m).
An eligible player may decline a claim and play. Claims already available to
the opponent on its PREVIOUS turn do not remain its out-of-turn actions.
If an announced move would mate, a correct claim chosen before playing it still
ends the current game as a draw; Play instead evaluates mate at the child.
Never execute the announced move before deciding the claim action.

## 5. Winning, holding, and the narrow projection bridge

Clock-free named-winner predicates are the frozen `MateWithin σ n q` and
`ForceMate σ q = ∃n, MateWithin σ n q`. They do not know h or H.

For this design write `RW σ n s` for mate forced within at most n ACTUAL BOARD
PLIES. A correct claim is a zero-ply terminal draw, never a mate target. Let
`Goal σ s := MateGoal σ q`. Let `Ongoing` be §4's nonterminal test and `s→t`
mean an actual Play transition (claims are not such transitions). Define:

```
RW σ 0 s := Goal σ s
RW σ (n+1) s := Goal σ s OR
  (Ongoing s AND
    ((q.turn=σ AND ∃t, s→t AND RW σ n t) OR
     (q.turn=σ.opp AND NOT CanClaim(s) AND
      (∃t, s→t) AND ∀t, s→t → RW σ n t)))
RuleForceMate σ s := ∃n, RW σ n s
```

This recurrence is the finite-rank game of §4: the named winner existentially
chooses and can ignore draw claims; EVERY defender move and claim is quantified.
A defender's available correct claim prevents forcing. Nonempty move branches
exclude vacuous stalemate wins. Automatic-draw children remain in the universal
reply set, and cannot satisfy RW. Terminal wins are board mate only; adding
resignation or flag-fall wins would change the projection obligation.

Define `RuleHold c s` separately as existence of a c-strategy for which every
opponent continuation avoids a terminal win by c.opp. It may obtain a correct
claim or any other board draw. A complete infinite play, if any, counts as
holding (no finite mate), not as a proved FIDE terminal result. Equivalence of
this strategy definition to the complement of the opponent's finite forcing
predicate, determinacy and termination of the full history game are additional
obligations. No unproved win/draw/loss trichotomy is installed as a definition.
Clock-free holding uses the corresponding no-history game and the same explicit
infinite-play convention. Rule-aware holding need not erase to clock-free
holding: a defensive claim may be the only holding action.

### EC-C022 — proposed generic finite-budget erasure theorem

First formalise a SMALL abstract layer, not all of §2–4. Let X be a state type
with erasure e:X→Position, BoardStep, Ongoing and CanClaim. Use the recurrence
above with Goal=`MateGoal σ (e s)`. Require, at EVERY ongoing state:

(A) BoardStep s t implies `Legal (e s) (e t)`.
(B) For EVERY r with `Legal (e s) r`, there exists t with BoardStep s t and e t=r.
(C) Ongoing s implies `¬ DeadK (e s)`.

No history lift may delete a raw legal reply just because its child draws.
Subject to A–C, the EXACT proposed statement is:

**For all X, layers satisfying A–C, σ, n and s,
`RW σ n s → MateWithin σ n (e s)`. Consequently rule forcing implies clock-free
forcing.** X, erasure and the step relation do not depend on σ or n.

Paper derivation: induction on n. At zero, Goal is the frozen MateGoal. In the
successor terminal branch use the same goal. In an ongoing strong branch,
(A) projects the chosen move and induction projects its child budget; (C)
provides the frozen nondeadness guard. In a weak branch, (A) projects a witness
of nonemptiness. For an ARBITRARY raw Legal successor r, (B) supplies a lifted
t; the universal premise and induction give `MateWithin σ n r`. Keep the same
turn and use (C). Discarding the NOT CanClaim guard is sound in this direction.
These are exactly the branches of frozen MateWithin, with the SAME ply budget.
Existentially quantify n for the forcing corollary.

Status remains **PROPOSED** pending an explicit local audit/Gate L and Lean
Gate F. The derivation above is a design argument, not a formal theorem. The
abstract result would not certify that a concrete history implementation meets
A–C or matches the FIDE clauses. Those are separately named instantiation
obligations. No decidability, board enumeration, strategy table, KRK hypothesis,
clock bound or repetition compression is needed for this first bridge.

### Why mere erasure does not prove the converse

`ForceMate σ q` supplies some n, not a numerical n that fits a clock. With the
same q, a weak player at h=99 may have an intended-move fifty-move claim, or
rep(s)=3 may allow ClaimNow. A clock-free win survives neither option. A state
at h=150 already automatically draws unless it is the threshold mate endpoint.
Erasing those data does not restore a rule-aware strategy. A move graph that
prunes draw-ending defender replies can even make the FORWARD projection false;
A–C are essential, not implicit consequences of the word “erasure”.

### Proposed sufficient-budget lifting plan (later, not EC-C022)

Take a concrete finite clock-free winning tree T with bound n, rooted at the
erasure of an admissible state s. Strong nodes retain their chosen move;
defending nodes retain ALL legal moves. Terminal leaves are actual named mate.
A deliberately conservative sufficient certificate is:

- h(s)+n < 100; after k plies, h≤h(s)+k, including resets;
- for EVERY prefix represented by T, the full history including that prefix
  has occurrence count at most TWO for its current key.

The second clause includes each child of EVERY defending announced legal move,
so also excludes intended repetition claims. It includes the root and earlier
history counts, not just repeats generated by T. It is a separate certificate
about this strategy tree and H, not inferred from finite rank. At a nonterminal
prefix of length k<n, a prospective next move has h'≤h(s)+k+1<100, so neither
current nor intended fifty-move claims arise; automatic 75-move draws cannot
arise. No node reaches threefold or fivefold. Clock-free winning prefixes are
not dead or stalemated. Induction can therefore instantiate the rule recurrence
along T with the same bound. Children after a zeroing draw cannot occur in a
clock-free winning tree, since dead KK refutes forcing.

Prove a finite-tree extraction/coverage lemma, clock-update inequality,
repetition-prefix certificate, terminal preservation and Ongoing preservation
before claiming this lifting theorem. The certificate is sufficient, not
necessary: it deliberately excludes wins where the winner may safely decline
its own threefold claim and wins on a draw threshold. No bound below 100 or
such repetition certificate has yet been proved for ALL KRK inputs.

## 6. First distance target and conventions

The first target is a **proved upper bound in plies to named opponent mate**,
`RW σ n s`, with explicit clock/history hypotheses. It is not exact DTM and is
not DTZ. Zero at actual named mate; a mating board move counts one; a rook
capture to KK is a draw, not zero-distance mate. Terminal draws and a win for
the other colour have no finite mate bound for σ. Failed availability of a
finite bound is denoted ∞ in any later distance notation, not zero or a
negative signed distance.

For specification only define `Dσ(s)=min{n | RW σ n s}`, or ∞ if empty. On
ongoing states its intended minimax equations are:

- σ to move: one plus the minimum Dσ over legal board-move children; a chosen
  correct draw claim has value ∞ for the mate objective and cannot improve it;
- σ.opp to move: ∞ if any correct claim is available, otherwise one plus the
  maximum Dσ over EVERY legal board-move child;
- named mate: zero; all other terminal outcomes: ∞; empty move sets never use
  a default min/max zero to create a win.

Board branching is finite; extrema and equivalence of these equations with RW
must be proved before implementation claims. Claim actions consume zero board
plies but end in a draw; they are not a gratuitous extra move before a mate.
Dσ depends on h and H. The clock-free analogue uses frozen MateWithin; neither
has been evaluated to an exact numeral. A full move is a pair of plies only
when the starting/ending convention is specified; do not silently round D/2.

A later custom zero-or-mate target must state whether a successful first event
is a pawn move, capture or mate, and require the resulting branch to preserve
the intended winning outcome. Counting a defender's rook capture to dead KK
as a successful “zero” would misclassify a draw as progress. Distances to a
future zeroing move start at one for that move; current h=0 is not a future
zeroing event. This document does NOT assert those are exact Syzygy conventions.
No Syzygy source or table was consulted. Exact five-valued WDL, cursed/blessed
categories, DTZ signs, zero/mate encoding, rounding and optimality criteria
require a separately sourced semantic comparison and proofs, not relabelling
this custom mate-bound predicate. Parity also needs a full admissible-input
coverage theorem, rule-aware outcomes/holding, and exact distance correctness.

## 7. Adversarial controls and outstanding obligations

| Fixed control | Expected result / failure caught |
|---|---|
| White Kc6/Ra1, Black Kc8, White Ra8#; h=149 before the move | Conditional on a compatible ongoing history, Play ends in mate at h=150; a terminal evaluator must not draw before checking mate. Geometry is the existing opposed-edge mating family; no compatible full history is asserted here. |
| White Kf6/Rg7, Black Kh8, Black turn | Protected rook but stalemate. Frozen `protected_corner_reentry_stalemate` supplies the local control; no vacuous universal-reply win. |
| White Kh8/Rb2, Black Kb1, Black turn | Kxb2 legally gives KK; Ka1 is also a legal escape. Optional capture suffices to obstruct strong forcing; one winning continuation is insufficient. This geometry is a paper control here, not a new compiled test. |
| White Kb2/Rh3, Black Kc4, White turn; Kc2 Kb4 Kb2 Kc4 | Frozen `phase_image_chase_cycle` returns the exact Position after four plies; h increases by four and repetition counts rise. Raw Position equality is not history-state equality. |
| Ongoing weak turn, h=99, legal nonzeroing move m, rep below thresholds | ClaimIntended(m) draws BEFORE execution; checking ClaimNow alone misses it. Contrast a legal zeroing m, whose h' is zero. |
| Same q with h=0 versus h=99/150, or current key count 1 versus 3/5 | Claim/automatic-draw options differ despite identical erasure. These pairs need compatible-prefix witnesses before they become full FIDE-position counterexamples; they already expose missing data in an unrestricted state definition. |
| Same board/turn, blocked castle with right retained versus right lost; raw ep without legal capture | Preserve the first key distinction; erase the ineffective ep distinction. Pinned ep is a required later key test. |

No new diagnostic was executed to certify these controls. Existing frozen
controls are cited as existing evidence, not rerun. The initial scope is a
mathematical specification; local examples cannot establish general rule-aware
outcomes or a class distance theorem.

Obligation graph (each arrow is a dependency, not an accomplished proof):

```
A–C abstract layer + finite-rank recurrence ──> EC-C022 same-budget projection
FIDE clauses + legal traces ──> concrete key/update/terminal/claim layer
concrete layer correctness ──> A–C instantiation ──> rule-win ⇒ frozen ForceMate
explicit KRK winning tree + clock budget + repetition certificate
    + concrete layer correctness ──> sufficient-budget lifting / mate upper bound
holding + outcome coverage + exact minimax + convention comparison ──> WDL/DTZ parity
```

**Chosen next task:** S033 proves only EC-C022's generic same-budget projection
and its existential corollary in new modules, after explicit local audit. It
must not turn the future concrete FIDE interface obligations into axioms or
mark their instantiation solved. Concrete repetition-key correctness, legal
history invariants, procedural extensions, numerical KRK bounds and Syzygy
conventions remain unproved. No frozen source or manifest needs modification.
