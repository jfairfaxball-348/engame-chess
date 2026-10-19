# EC-C023 — Concrete raw kernel move traces and complete append lifting

S035. Classical inductively represented legal histories; no novelty claim.
Sources: the repository's frozen Position, Move, isLegal/play, Legal and
ReachK/Arisen definitions; S032 history specification; EC-T0020's abstract
soundness/completeness boundary. No engine, tablebase, enumeration, strategy
values or per-position certificates are used.

## Concrete data, not just a reachability proposition

Define an indexed inductive **Type** `Trace q`:

- `start : Trace initial` is the empty trace, with the standard initial
  Position as its exact root and endpoint.
- Given t:Trace q, a full Move m (source, destination and promotion field), and
  h:isLegal q m=true, `snoc t m h : Trace (play q m)`.

The previous trace and Move are data; h is a proof-only field. This is not the
frozen Prop `ReachK initial q` in a new wrapper. Induction over the data can
read the ordered actual moves, their source positions and played endpoints.
Full Position values retain board, turn, castling rights and raw ep flags.
No arbitrary seed position, flags, clock or count vector is silently admitted.

Define ordered `Trace.moves` by [] at start and `moves(t) ++ [m]` at snoc.
Define ordered `Trace.positions` by [initial] at start and
`positions(t) ++ [play q m]` at snoc. Thus position endpoints include both the
root and current position, while the empty trace contains no moves. Proof-only
legality evidence does not identify different Move data or discard the prefix.
The positions are derived from the indexed trace; no extra unverified snapshot
list is supplied by the caller.

A state s contains an endpoint q and data t:Trace q. Define erase(s)=q,
initialState=(initial,start), and for EVERY m and legality proof h at erase(s):

`append(s,m,h) = (play (erase s) m, snoc s.trace m h)`.

This is a total append operation for a legal move at ANY raw trace endpoint,
independent of material, colour, eventual outcome or chosen strategy. Trace
validity is preserved by the constructor's type and supplied legality proof.

## Main statements and derivations

### Append retention and exact endpoint

For every s,m,h, the appended state has:

1. erased endpoint `play (erase s) m`;
2. moves exactly `s.trace.moves ++ [m]`;
3. positions exactly `s.trace.positions ++ [play (erase s) m]`;
4. number of recorded moves `s.trace.moves.length + 1`.

Proof: unfold append and the snoc recursion. The first three equations are
constructor/definition equalities. The fourth follows from list append length
and singleton length. No replay validity assumption is lost: the appended
trace has precisely the played-position index by construction. This proves
full prefix retention, not merely existence of some trace to the same board.

### Raw board-step soundness

Define `RawBoardStep s t` by existence of a Move m, proof
h:isLegal (erase s) m=true, and equality `t=append s m h`.
It is NOT a relation allowing arbitrary unrelated histories with legally
related endpoints. In particular, every such step preserves the actual prefix.

For every s,t, RawBoardStep s t implies Legal (erase s) (erase t).
Proof: extract m,h and substitute t. Erasing append gives the played position;
use the kernel Legal witness m,h and reflexivity of that endpoint equality.

### Complete lifting of EVERY raw legal reply

For EVERY s and EVERY kernel position r,

`Legal (erase s) r → ∃ t, RawBoardStep s t ∧ erase t = r`.

Proof: the kernel Legal premise supplies m,h and r=play (erase s) m. Choose
EXACTLY append(s,m,h). Its RawBoardStep witness is m,h with equality reflexive;
its erasure is r by the supplied target equality. There is no filtering for
wins, captures, zeroing, deadness, clock expiration or repetition. Therefore
all raw replies, including children that would immediately draw under a later
history classifier, remain covered. No cooperation or winning-continuation
hypothesis is present.

### Endpoint origin (support lemma)

For every q and t:Trace q, Arisen q holds in the FROZEN raw-kernel sense.
Induct on t. At start use ReachK.refl initial. At snoc, the induction hypothesis
is ReachK initial q and m,h give Legal q (play q m). Append that legal edge
using ReachK.tail. This does not turn ReachK into no-earlier-terminal FIDE
admissibility; it is a one-way forgetting of the richer trace data.

## Adversarial boundary and next obligations

Root is fixed initial, not an arbitrary KRK snapshot. All actual Move data,
including promotion choice, are retained. Both turn orientations are covered
through the generic kernel move witness; no white-only or rook-only move
restriction occurs. Distinct histories with identical erasure are not thereby
identified; ordered prefix data remain part of the state.

These are **RAW** kernel traces. No halfmove counter, repetition key, Ongoing,
claim classifier or no-earlier-terminal condition is defined. Kernel Legal
alone can permit continuation after a rule draw. The append theorem must still
cover that raw legal edge; it does not certify that an actual FIDE game could
continue there. Later admissibility must constrain earlier parent prefixes,
while allowing a child which has just become terminal. It cannot discard an
adverse child to fabricate a forcing win.

This component provides concrete data and unrestricted move soundness/lifting
relevant to EC-T0020 fields A/B. It does NOT instantiate the whole Layer:
ongoing nondeadness (C), real claims/terminals and concrete FIDE admissibility
remain open. No converse strategy theorem, holding/determinacy, clock reset,
repetition equivalence, numerical KRK distance, DTM/DTZ, WDL/Syzygy parity or
initial-position value is claimed. Gate Z remains separate from Gate F.
