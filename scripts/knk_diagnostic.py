#!/usr/bin/env python3
"""Exhaustive K+N vs K diagnostic for EC-C003.

DIAGNOSTIC SUPPLEMENT ONLY: this is NOT a proof and NOT a tablebase. It reads no
external data and stores no evaluations. Moves are generated directly from FIDE
2023 Articles 3.1, 3.6 (knight: the eight (1,2)/(2,1) offsets, listed explicitly
below rather than derived from colour or distance), 3.8.1 (king: adjoining square)
and 3.9 (check). It does not use the colour argument of proofs/EC-C003_KNK.md, so
that argument is checked against an independent encoding.

Both material orientations are enumerated (White K+N vs Black K, and Black K+N vs
White K), with both sides to move. `check_geometry()` separately tests every
geometric claim used in lemmas N1 and N2 of the proof (and the one claim of the
S011 prompt that turned out to be false). `run(mutant=True)` gives the knight an
extra king step; mates must then appear (mutation test).
"""
import sys
import time

N = 8
SQUARES = [(x, y) for x in range(N) for y in range(N)]
KING_STEPS = [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)]
KNIGHT_STEPS = [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]
W, B = "W", "B"
OTHER = {W: B, B: W}


def on_board(x, y):
    return 0 <= x < N and 0 <= y < N


def steps_from(sq, steps):
    x, y = sq
    return {(x + dx, y + dy) for dx, dy in steps if on_board(x + dx, y + dy)}


def attacked_squares(kind, sq, mutant=False):
    """Squares a piece of `kind` on `sq` could capture on (Art. 3.1.2), ignoring
    self-check. Neither the king nor the knight can be obstructed (3.5 does not
    apply to them), so occupancy is irrelevant here."""
    if kind == "K":
        return steps_from(sq, KING_STEPS)
    if kind == "N":
        out = steps_from(sq, KNIGHT_STEPS)
        if mutant:
            out |= steps_from(sq, KING_STEPS)
        return out
    raise ValueError(kind)


def in_check(pos, colour, mutant=False):
    king = pos[(colour, "K")]
    return any(
        king in attacked_squares(kind, sq, mutant)
        for (c, kind), sq in pos.items() if c != colour
    )


def legal_moves(pos, to_move, mutant=False):
    """All FIDE-legal successor positions. No rooks or pawns: castling, promotion and
    en passant are impossible."""
    occupied = {sq: key for key, sq in pos.items()}
    out = []
    for (c, kind), sq in pos.items():
        if c != to_move:
            continue
        for dest in attacked_squares(kind, sq, mutant):
            victim = occupied.get(dest)
            if victim is not None and victim[0] == to_move:
                continue  # 3.1
            if victim is not None and victim[1] == "K":
                continue  # 1.4.1: the king is never captured
            nxt = dict(pos)
            if victim is not None:
                del nxt[victim]  # 3.1.1
            nxt[(c, kind)] = dest
            if in_check(nxt, to_move, mutant):
                continue  # 3.9.2
            out.append(nxt)
    return out


def d_inf(p, q):
    return max(abs(p[0] - q[0]), abs(p[1] - q[1]))


def col(sq):
    return (sq[0] + sq[1]) % 2


def run(orientations=(W, B), mutant=False):
    start = time.time()
    r = dict(placements=0, legal_states=0, checks_of_lone_king=0, checkmates=0,
             stalemates=0, legal_moves=0, captures_to_kk=0, closure_violations=0,
             lone_king_in_check_without_move=0, strong_side_in_check=0,
             checked_king_without_orthogonal_escape=0, double_checks=0,
             lone_king_escapes_by_capture=0)
    for strong in orientations:
        weak = OTHER[strong]
        knk = frozenset({(strong, "K"), (strong, "N"), (weak, "K")})
        kk = frozenset({(W, "K"), (B, "K")})
        for sk in SQUARES:
            for ns in SQUARES:
                if ns == sk:
                    continue
                for wk in SQUARES:
                    if wk in (sk, ns):
                        continue
                    for t in (W, B):
                        r["placements"] += 1
                        pos = {(strong, "K"): sk, (strong, "N"): ns, (weak, "K"): wk}
                        # Legal state: the side NOT to move is not in check (3.9.2
                        # applied to the move that produced the position).
                        if in_check(pos, OTHER[t], mutant):
                            continue
                        r["legal_states"] += 1
                        if in_check(pos, strong, mutant):
                            r["strong_side_in_check"] += 1
                        succ = legal_moves(pos, t, mutant)
                        r["legal_moves"] += len(succ)
                        mover_in_check = in_check(pos, t, mutant)
                        if t == weak and mover_in_check:
                            r["checks_of_lone_king"] += 1
                            if not succ:
                                r["lone_king_in_check_without_move"] += 1
                            checkers = [kind for (c, kind), sq in pos.items()
                                        if c == strong and wk in attacked_squares(kind, sq, mutant)]
                            if len(checkers) > 1:
                                r["double_checks"] += 1
                            dests = {s[(weak, "K")] for s in succ}
                            if not any(d_inf(d, wk) == 1 and col(d) != col(wk) for d in dests):
                                r["checked_king_without_orthogonal_escape"] += 1
                            if any((strong, "N") not in s for s in succ):
                                r["lone_king_escapes_by_capture"] += 1
                        if not succ:
                            if mover_in_check:
                                r["checkmates"] += 1
                            else:
                                r["stalemates"] += 1
                        for s in succ:
                            m = frozenset(s)
                            # Closure: successor is a legal state of KNK or KK.
                            ok = not in_check(s, t, mutant)
                            if m == kk:
                                r["captures_to_kk"] += 1
                                ok = ok and d_inf(s[(W, "K")], s[(B, "K")]) >= 2
                            elif m != knk:
                                ok = False
                            if not ok:
                                r["closure_violations"] += 1
    r["seconds"] = round(time.time() - start, 1)
    return r


def check_geometry():
    """Check each geometric claim of N1/N2 over the whole board. Returns a dict of
    counterexample counts (all expected 0) plus two expected-positive witness counts."""
    g = dict(knight_move_same_colour=0, knight_targets_not_8_offsets=0,
             knight_attacks_orth_neighbour_of_checked_king=0,
             knight_attacks_two_neighbours_of_checked_king=0,
             checking_knight_adjacent=0, two_knight_targets_orth_adjacent=0,
             king_covers_both_h_and_v=0, h_or_v_off_board=0,
             # Witness counts, expected POSITIVE:
             knight_attacks_diag_neighbour_of_checked_king=0,
             two_knight_targets_diag_adjacent=0)
    for s in SQUARES:
        ts = steps_from(s, KNIGHT_STEPS)
        # Art. 3.6 restated: squares nearest s not on its rank, file or diagonal.
        off = [t for t in SQUARES if t != s and t[0] != s[0] and t[1] != s[1]
               and abs(t[0] - s[0]) != abs(t[1] - s[1])]
        dmin = min((t[0] - s[0]) ** 2 + (t[1] - s[1]) ** 2 for t in off)
        nearest = {t for t in off if (t[0] - s[0]) ** 2 + (t[1] - s[1]) ** 2 == dmin}
        if nearest != ts:
            g["knight_targets_not_8_offsets"] += 1
        for t in ts:
            if col(t) == col(s):
                g["knight_move_same_colour"] += 1
        for t in ts:
            for u in ts:
                if t < u:
                    dx, dy = abs(t[0] - u[0]), abs(t[1] - u[1])
                    if dx + dy == 1:
                        g["two_knight_targets_orth_adjacent"] += 1
                    if dx == 1 and dy == 1:
                        g["two_knight_targets_diag_adjacent"] += 1
        # s is the knight square; every k in ts is a king it checks.
        for k in ts:
            if d_inf(s, k) <= 1:
                g["checking_knight_adjacent"] += 1
            nbrs = steps_from(k, KING_STEPS)
            hit = [q for q in nbrs if q in ts]
            if len(hit) > 1:
                g["knight_attacks_two_neighbours_of_checked_king"] += 1
            for q in hit:
                if col(q) != col(k):
                    g["knight_attacks_orth_neighbour_of_checked_king"] += 1
                else:
                    g["knight_attacks_diag_neighbour_of_checked_king"] += 1
    # N2 step: h, v toward the interior; no king at distance >= 2 from k covers both.
    for k in SQUARES:
        a, b = k
        h = (a + (1 if a == 0 else -1), b)
        v = (a, b + (1 if b == 0 else -1))
        if not (on_board(*h) and on_board(*v)):
            g["h_or_v_off_board"] += 1
        for K in SQUARES:
            if d_inf(K, k) >= 2 and d_inf(K, h) <= 1 and d_inf(K, v) <= 1:
                g["king_covers_both_h_and_v"] += 1
    return g


EXPECTED_ZERO = ["checkmates", "closure_violations", "lone_king_in_check_without_move",
                 "strong_side_in_check", "checked_king_without_orthogonal_escape",
                 "double_checks", "lone_king_escapes_by_capture"]
GEOMETRY_POSITIVE = ["knight_attacks_diag_neighbour_of_checked_king",
                     "two_knight_targets_diag_adjacent"]


def main():
    g = check_geometry()
    print("== geometry (N1/N2 claims) ==")
    for k, v in g.items():
        print(f"{k}: {v}")
    geo_bad = [k for k in g if (k in GEOMETRY_POSITIVE and g[k] == 0)
               or (k not in GEOMETRY_POSITIVE and g[k] != 0)]
    print("== exhaustive K+N vs K ==")
    r = run()
    for k, v in r.items():
        print(f"{k}: {v}")
    print("== mutation: knight with an extra king step, one orientation ==")
    m = run(orientations=(W,), mutant=True)
    print(f"checkmates: {m['checkmates']}")
    print(f"lone_king_in_check_without_move: {m['lone_king_in_check_without_move']}")
    bad = [k for k in EXPECTED_ZERO if r[k] != 0] + geo_bad
    if r["placements"] != 2 * 64 * 63 * 62 * 2:
        bad.append("placements")
    if m["checkmates"] == 0:
        bad.append("mutation_not_detected")
    if bad:
        print("KNK DIAGNOSTIC FAILED:", bad)
        return 1
    print("KNK DIAGNOSTIC PASSED (supplementary evidence, not a proof)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
