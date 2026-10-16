#!/usr/bin/env python3
"""Exhaustive two-king diagnostic for EC-C001.

DIAGNOSTIC SUPPLEMENT ONLY: this is NOT a proof and NOT a tablebase. It
enumerates every (white king, black king, side to move) triple on the 8x8
board with an independently coded move generator and checks the finite facts
the paper proof in proofs/EC-C001_KK.md relies on. No external data is read.

The move generator here deliberately does NOT reuse the Chebyshev formula:
attacks and moves are generated from the eight king offsets plus bounds
checks, then compared against d_inf.
"""
import argparse
from collections import deque

N = 8
OFFSETS = [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)]
SQUARES = [(x, y) for x in range(N) for y in range(N)]
WHITE, BLACK = "W", "B"


def on_board(s):
    return 0 <= s[0] < N and 0 <= s[1] < N


def d_inf(p, q):
    return max(abs(p[0] - q[0]), abs(p[1] - q[1]))


def king_targets(s):
    """Squares a king on s could move to / capture on (FIDE 3.8.1), ignoring check."""
    return {(s[0] + dx, s[1] + dy) for dx, dy in OFFSETS if on_board((s[0] + dx, s[1] + dy))}


def attacks(s, q):
    """FIDE 3.1.2/3.1.3: a king on s attacks q iff it could capture there by 3.8.1."""
    return q in king_targets(s)


def in_check(state, colour):
    w, b, _ = state
    own, opp = (w, b) if colour == WHITE else (b, w)
    return attacks(opp, own)


def legal_moves(state):
    """All FIDE-legal moves in a kings-only position (no castling: no rooks)."""
    w, b, t = state
    mover, other = (w, b) if t == WHITE else (b, w)
    result = []
    for dest in king_targets(mover):
        if dest == other:
            continue  # would capture the king: forbidden (Art. 1.4.1)
        if attacks(other, dest):
            continue  # would expose own king to check (Art. 3.9.2)
        nxt = (dest, b, BLACK) if t == WHITE else (w, dest, WHITE)
        result.append(nxt)
    return result


def admissible(state):
    return d_inf(state[0], state[1]) >= 2


def run():
    all_states = [(w, b, t) for w in SQUARES for b in SQUARES for t in (WHITE, BLACK)]
    adm = [s for s in all_states if admissible(s)]
    report = {}
    report["states_total"] = len(all_states)
    report["admissible_states"] = len(adm)
    report["admissible_placements"] = len({(w, b) for w, b, _ in adm})

    report["attack_eq_dinf1_violations"] = sum(
        1 for p in SQUARES for q in SQUARES if attacks(p, q) != (d_inf(p, q) == 1)
    )
    report["admissible_in_check"] = sum(
        1 for s in adm for c in (WHITE, BLACK) if in_check(s, c)
    )
    closure_violations = 0
    turn_violations = 0
    one_king_moved_violations = 0
    move_count = 0
    no_move_states = 0
    for s in adm:
        moves = legal_moves(s)
        if not moves:
            no_move_states += 1
        for q in moves:
            move_count += 1
            if not admissible(q):
                closure_violations += 1
            if q[2] == s[2]:
                turn_violations += 1
            moved = [i for i in (0, 1) if q[i] != s[i]]
            expected = 0 if s[2] == WHITE else 1
            if moved != [expected] or d_inf(s[expected], q[expected]) != 1:
                one_king_moved_violations += 1
    report["legal_moves_total"] = move_count
    report["step_closure_violations"] = closure_violations
    report["turn_flip_violations"] = turn_violations
    report["wrong_king_or_distance_violations"] = one_king_moved_violations
    report["admissible_states_without_legal_move"] = no_move_states

    # Checkmate / stalemate over the whole admissible set.
    report["checkmates"] = sum(1 for s in adm if in_check(s, s[2]) and not legal_moves(s))
    report["stalemates"] = sum(1 for s in adm if not in_check(s, s[2]) and not legal_moves(s))

    # Independent BFS from every admissible state: reachable states stay admissible
    # and never contain a checked king. (Redundant with closure; kept as a cross-check.)
    seen = set(adm)
    queue = deque(adm)
    bad = 0
    while queue:
        s = queue.popleft()
        if not admissible(s) or in_check(s, WHITE) or in_check(s, BLACK):
            bad += 1
        for q in legal_moves(s):
            if q not in seen:
                seen.add(q)
                queue.append(q)
    report["bfs_reached_states"] = len(seen)
    report["bfs_bad_states"] = bad

    # Non-admissible placements: every adjacent placement puts BOTH kings in check,
    # confirming such a position cannot follow any legal move (Art. 3.9.2).
    adjacent = [s for s in all_states if d_inf(s[0], s[1]) == 1]
    report["adjacent_states"] = len(adjacent)
    report["adjacent_states_not_double_check"] = sum(
        1 for s in adjacent if not (in_check(s, WHITE) and in_check(s, BLACK))
    )
    return report


EXPECTED = {
    "states_total": 8192,
    "admissible_states": 7224,
    "admissible_placements": 3612,
    "attack_eq_dinf1_violations": 0,
    "admissible_in_check": 0,
    "step_closure_violations": 0,
    "turn_flip_violations": 0,
    "wrong_king_or_distance_violations": 0,
    "checkmates": 0,
    "bfs_bad_states": 0,
    "adjacent_states_not_double_check": 0,
}


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    report = run()
    for key, value in report.items():
        print(f"{key}: {value}")
    failures = [k for k, v in EXPECTED.items() if report[k] != v]
    if failures:
        raise SystemExit(f"DIAGNOSTIC MISMATCH: {', '.join(failures)}")
    print("DIAGNOSTIC CONSISTENT with EC-C001 lemmas (supplementary evidence, not a proof)")


if __name__ == "__main__":
    main()
