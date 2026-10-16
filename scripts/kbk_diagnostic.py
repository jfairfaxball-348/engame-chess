#!/usr/bin/env python3
"""Exhaustive K+B vs K diagnostic for EC-C002.

DIAGNOSTIC SUPPLEMENT ONLY: this is NOT a proof and NOT a tablebase. It reads no
external data and stores no evaluations. Moves are generated directly from FIDE
2023 Articles 3.1, 3.5 (bishop: diagonal, may not pass over pieces), 3.8.1
(king: adjoining square) and 3.9 (check), by walking rays square by square. It
deliberately does not use the colour-complex argument of proofs/EC-C002_KBK.md,
so that argument is checked against an independent encoding.

Both material orientations are enumerated (White K+B vs Black K, and Black K+B
vs White K), with both sides to move.
"""
import sys
import time

N = 8
SQUARES = [(x, y) for x in range(N) for y in range(N)]
KING_STEPS = [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)]
DIAGONALS = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
W, B = "W", "B"
OTHER = {W: B, B: W}


def on_board(x, y):
    return 0 <= x < N and 0 <= y < N


def attacked_squares(kind, sq, occupied):
    """Squares a piece of `kind` on `sq` could capture on (Art. 3.1.2), ignoring self-check."""
    x, y = sq
    out = set()
    if kind == "K":
        for dx, dy in KING_STEPS:
            if on_board(x + dx, y + dy):
                out.add((x + dx, y + dy))
    elif kind == "B":
        for dx, dy in DIAGONALS:
            cx, cy = x + dx, y + dy
            while on_board(cx, cy):
                out.add((cx, cy))
                if (cx, cy) in occupied:
                    break  # Art. 3.5: may not move over an intervening piece
                cx, cy = cx + dx, cy + dy
    return out


def in_check(pos, colour):
    occupied = set(pos.values())
    king = pos[(colour, "K")]
    return any(
        king in attacked_squares(kind, sq, occupied)
        for (c, kind), sq in pos.items() if c != colour
    )


def legal_moves(pos, to_move):
    """All FIDE-legal successor positions. No rooks or pawns: castling, promotion and
    en passant are impossible."""
    occupied = {sq: key for key, sq in pos.items()}
    out = []
    for (c, kind), sq in pos.items():
        if c != to_move:
            continue
        for dest in attacked_squares(kind, sq, set(occupied)):
            victim = occupied.get(dest)
            if victim is not None and victim[0] == to_move:
                continue  # 3.1
            if victim is not None and victim[1] == "K":
                continue  # 1.4.1: the king is never captured
            nxt = dict(pos)
            if victim is not None:
                del nxt[victim]  # 3.1.1
            nxt[(c, kind)] = dest
            if in_check(nxt, to_move):
                continue  # 3.9.2
            out.append(nxt)
    return out


def d_inf(p, q):
    return max(abs(p[0] - q[0]), abs(p[1] - q[1]))


def material(pos):
    return frozenset(pos)


def run(orientations=(W, B)):
    start = time.time()
    r = dict(placements=0, legal_states=0, checks_of_lone_king=0, checkmates=0,
             stalemates=0, legal_moves=0, captures_to_kk=0, closure_violations=0,
             lone_king_in_check_without_move=0, strong_side_in_check=0)
    for strong in orientations:
        weak = OTHER[strong]
        kbk = frozenset({(strong, "K"), (strong, "B"), (weak, "K")})
        kk = frozenset({(W, "K"), (B, "K")})
        for sk in SQUARES:
            for bs in SQUARES:
                if bs == sk:
                    continue
                for wk in SQUARES:
                    if wk in (sk, bs):
                        continue
                    for t in (W, B):
                        r["placements"] += 1
                        pos = {(strong, "K"): sk, (strong, "B"): bs, (weak, "K"): wk}
                        # Legal state: the side NOT to move is not in check (3.9.2
                        # applied to the move that produced the position).
                        if in_check(pos, OTHER[t]):
                            continue
                        r["legal_states"] += 1
                        assert d_inf(sk, wk) >= 2
                        if in_check(pos, strong):
                            r["strong_side_in_check"] += 1
                        succ = legal_moves(pos, t)
                        r["legal_moves"] += len(succ)
                        mover_in_check = in_check(pos, t)
                        if t == weak and mover_in_check:
                            r["checks_of_lone_king"] += 1
                            if not succ:
                                r["lone_king_in_check_without_move"] += 1
                        if not succ:
                            if mover_in_check:
                                r["checkmates"] += 1
                            else:
                                r["stalemates"] += 1
                        for s in succ:
                            m = material(s)
                            # Closure: successor is a legal state of KBK or KK.
                            ok = not in_check(s, t)
                            if m == kk:
                                r["captures_to_kk"] += 1
                                ok = ok and d_inf(s[(W, "K")], s[(B, "K")]) >= 2
                            elif m != kbk:
                                ok = False
                            if not ok:
                                r["closure_violations"] += 1
    r["seconds"] = round(time.time() - start, 1)
    return r


EXPECTED_ZERO = ["checkmates", "closure_violations", "lone_king_in_check_without_move",
                 "strong_side_in_check"]


def main():
    r = run()
    for k, v in r.items():
        print(f"{k}: {v}")
    bad = [k for k in EXPECTED_ZERO if r[k] != 0]
    if bad or r["placements"] != 2 * 64 * 63 * 62 * 2:
        print("KBK DIAGNOSTIC FAILED:", bad)
        return 1
    print("KBK DIAGNOSTIC PASSED (supplementary evidence, not a proof)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
