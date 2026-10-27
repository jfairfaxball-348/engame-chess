# KRK: complete weak-turn RAW history band h >= 93

Locally Lean-verified, unfrozen. Full KRK remains OPEN.

## Exact statement

For every admitted ongoing RAW KRK history, either strong colour, every board
orientation and weak side to move, with h>=93, `KRKSixPlyHistory.Clear` is
equivalent to forced mate and `ActualWin`. Its complement is equivalent to
weak holding and to holding by both players. Minimum winning mate-within
bounds are exactly two, four or six board plies. This is not a completed FIDE
repetition-key or global DTZ correspondence claim.

## Explicit original-trace formula

Use the coordinate neighbour guard G(T): dInf(W,T)=1, T!=R,
dInf(K,T)>=2 and not RookSees(R,T,K,T). Require safe rook, h<99,
fewer than three current occurrences, and for every guarded T:

- fewer than two original occurrences of P=play(root,W->T);
- the [seventeen-point strong formula](KRK_FIVE_PLY_HISTORY.md) at (K,R,T),
  with the following exact substitutions for its history tests.

Let H be the original trace. For any candidate strong entry M after W->T,
put Q=play(P,M). Every later queried position V is evaluated by

    C1(V) = occurrences(H,V) + [key(P)=key(V)],
    C2(V) = C1(V) + [key(Q)=key(V)].

The post-entry weak current-key test uses C1(Q)<2. Its intended reply and
later entry/reply key tests use C2. The corresponding root clock conditions
become h<97 for the post-entry weak deadline and h<95 for the inner two-key
entry. All board positions are produced by actual native play. Neither
indicator is silently dropped, and all flags in both appended keys are kept.

`KRKFiveWeakPrefix` defines these tests using the finite seventeen-point and
seven-slot coordinate catalogues. It proves exact equivalence to the strong
five-ply formula on the actual first appended trace. The formulas contain no
future-outcome or legal-move predicate, no recursive value definition and no
per-position outcomes. Their only branches are coordinate guards, the finite
catalogues, rook line coordinates and original-key equality/count tests.

## Proof and exact distances

Necessity: weak forcing implies a safe rook and no current/intended claim.
Every actual guarded reply reaches an admitted strong child at h>=94, so the
complete five-ply theorem supplies exactly the substituted child formula.
The root h<99 and original first-key count tests are necessary claim tests.

Sufficiency: every actual weak move is one of the guarded canonical king
moves. The root tests exclude all current/intended claims. Each branch gives
the exact five-ply formula on its actual appended trace. Its kernel projection
proves nondead status and nonempty strong play; the clock and first-key bounds
prove that child is ongoing. Thus the five-ply rule certificate applies at
every child with a uniform bound, yielding a six-ply root certificate.

The shorter-distance tests are also exact at every clock:
`KRKFourPlyExact.rule_four_iff` identifies four-ply weak certificates with the
previous seven-slot global weak formula, and `rule_two_iff` identifies two
plies with `LastReply` plus absence of claims. RAW parity compression preserves
all claims and actual steps: weak three-ply certificates compress to two,
and weak five-ply certificates compress to four. Hence winning distance is
2 on `LastReply`, otherwise 4 on the previous global weak criterion, otherwise
6. This proves matching exclusions of bounds 1, 3 and 5 respectively.

Full aggregate `lake build`: PASS, 307 jobs. Public `AxiomCheck.lean`: PASS;
all new declarations depend only on subsets of propext, Classical.choice and
Quot.sound. No sorry/admit/new axiom or unsafe proof escape. No tablebase,
engine or stored position values were consulted. Frozen sources/manifests and
the ledger are unchanged; hosted CI/Palomar success is not asserted.

Next unresolved clock bands: strong h=92/93 and weak h=91/92, then lower
positive clocks. Deeper destination geometry and any castling alternatives
must be evaluated rather than replaced by generic outcome recursion. Full
terminal/capture coverage, FIDE correspondence and global WDL/DTZ remain open.
