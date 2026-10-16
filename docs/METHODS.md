# Methods, definitions and exclusions

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
