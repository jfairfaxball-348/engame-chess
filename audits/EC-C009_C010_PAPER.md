# S024 paper audit — EC-C009 and EC-C010

Same-agent adversarial audit (not independent external review), before Lean implementation. No novelty claimed.

- **Empty universal quantifier:** rejected the definition using only “all replies win”; the defender clause explicitly requires at least one legal successor. Terminal inversion proves stalemate cannot win.
- **Wrong-colour and zero-length mate:** winner is named; the base requires the opposite side to move and be checkmated. A pre-existing mate needs zero plies; the wrong-colour mate is excluded.
- **Deadness and clocks:** moves are disabled at dead states in the forcing predicate; soundness also independently excludes dead forcing states. Clock/repetition rules are absent and no FIDE WDL claim is made.
- **Optional versus forced capture:** Kh8/Rb3/Ka2 with Black to move is the proposed fixed kernel witness. One capture-to-KK reply refutes forcing despite a different live reply. This avoids conflating liveness, failure to force mate, and the full definition of a draw.
- **All defences:** the barrier proof begins by extracting an arbitrary kernel `Legal` move. Reusing only `step_sound` would be insufficient because it describes selected non-capturing model moves.
- **Hanging rook:** protection excludes rook capture using self-check after the move. It is not inferred merely from rook-line attacks.
- **Blocked rook ray:** an initial non-strict “king below or on the rook rank” proposal failed: Ke4/Rd4/Kg5 permits Kg4. Strict separation repairs the argument; king protection alone is insufficient to clear the ray.
- **Boundary and stalemate:** Kc6/Rb7/Ka8, Black to move, satisfies all barrier assumptions and has no legal move. The conclusion is a universal preservation statement only; the forcing defender rule requires nonemptiness separately. An empty upper region cannot satisfy y(R)<y(W).
- **Flags and orientation:** inverse move extraction excludes lone-side castling by absence of its rook. King movement has no pawn direction, so the rank argument is uniform in colour; no symmetry claim for the full general kernel is used.
- **Progress:** the barrier measure remains constant through a defender reply. No claimed descent, full forced-win theorem, distance bound or WDL result is smuggled into this prerequisite.

The symbolic proofs in `proofs/EC-C009_FORCING.md` and `proofs/EC-C010_KRK_CONFINEMENT.md` close these statements on paper. Their Gate F status requires observed compilation, declaration fidelity and axiom checks. Fixed configurations supply negative controls/non-vacuity only, not enumeration proofs of either general theorem.

- **Attempt to lift the barrier:** with S fixed strictly below R, any new rook rank above R is at least two ranks from S and loses king protection. The symbolic distance inequality is proved as `protected_rank_raise_unprotected`. The protected barrier is consequently a reply invariant, not yet a full strategy invariant; S025 must broaden safety rather than assume a nonexistent protected advance.
