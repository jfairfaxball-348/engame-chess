# Methods, definitions and exclusions

## Solving terminology and scope
The ultimate ambition is **ultra-weak solving as a draw**: prove the game-theoretic value of the *standard initial position* is a draw, within a fully specified rules/termination model. This need not yield a constructive strategy or even one recommended opening move. It does not claim the draw value is currently known.

A **weak** solution would additionally exhibit an effective way to achieve the initial position's game-theoretic value against arbitrary opposition; a **strong** solution covers all legal positions. A value proof may entail that strategies exist without specifying them. Do not confuse these goals with the much stronger active intermediate programme of proving exact outcomes of all positions in material classes through seven pieces. Neither local forced-mate proofs nor mathematical strategy lemmas are prohibited by the ultra-weak ambition; they can be useful tools without constituting a playing oracle.

**Priority order:** operational seven-piece tablebase parity, pursued through the live KRK obligation with mathematical proof → Lean formalisation → verified freeze, without mandatory per-session reporting. The initial-position draw remains a distant, conjectural objective, not a replacement task.

## Allowed mathematics
Combinatorial game theory, turn-based reachability games, adversarial quantification (exists move / for all replies), finite/infinite plays, game graphs, graph kernels, fixed points, invariants, metric and lattice geometry, piece-attacks as functions, parity/colouring, symmetries, symbolic logic, and elementary geometry of boundaries.

Every theorem must say whether it proves:
- *possible mate* (there exists a legal continuation ending in mate);
- *forced mate* (a winning strategy against all legal defences, with exact draw/termination model);
- *dead position* (there exists no legal continuation ending in mate for either side);
- *a draw under FIDE rules* (rules applied to the mathematical result);
- *a bound* (number of moves, distance, branching factor, minimax rank, etc.).

Do **not** identify forced-mate failure with dead position.

## Local verification, not tablebase substitution
No Syzygy, Nalimov, Lomonosov, downloaded DTZ/DTM/WDL arrays, tablebase APIs, derivatives or cited tablebase evaluations. No chess engine as theorem oracle. Small programs written from independently specified movement functions may be used to find counterexamples and test finite boundary cases. Such programs are *auxiliary* until their results are reduced to a human-checkable mathematical proof or a formally certified exhaustive argument.

Constructive/inductive use of game graphs and retrograde reasoning is allowed as mathematics; importing a solved table of positions is not.

## Rule and claim versioning
Use FIDE Laws of Chess effective 2023 as initial reference: https://handbook.fide.com/chapter/E012023. Each claim pins its own edition. Distinguish position geometry (static), hypothetical legal-play graph (dynamic), and actual terminated game (normative). Model positions as *reachable from initial play* only where the theorem needs global reachability.

## Publication posture
These initial results are expected to be classical. The programme's early purpose is correctness, faithful formalisation and a trustworthy accumulating library, not novelty inflation.
