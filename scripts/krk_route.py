#!/usr/bin/env python3
"""Strategy simulator for EC-C008 (K+R vs K, strong side to move, is never dead).

SUPPLEMENTARY ONLY. It plays one explicit cooperative route, the one described in
proofs/EC-C008_KRK_LIVE.md, from every legal strong-to-move K+R vs K state. Every move
the route chooses is checked against the independent legal-move generator of
krk_diagnostic.py, and the route must end in checkmate. It is not a search: each move
is chosen by the route's fixed rules. The simulator exists to find cases the paper
route mishandles, and to report route lengths.

Frame: the strong side is White, its king S, its rook R; the lone king L. The route
first applies a reflection so that S = (sx, sy) has sx <= 3 and sy >= 2. Reflections
preserve king and rook geometry, so they map legal moves to legal moves.
"""
import sys
from collections import deque

import krk_diagnostic as kd

W, B = kd.W, kd.B
N = 8


def reflect(sq, fx, fy):
    x, y = sq
    return (7 - x if fx else x, 7 - y if fy else y)


def normalise(S, R, L):
    fx = S[0] > 3
    fy = S[1] < 2
    return reflect(S, fx, fy), reflect(R, fx, fy), reflect(L, fx, fy)


def dinf(p, q):
    return max(abs(p[0] - q[0]), abs(p[1] - q[1]))


class RouteError(Exception):
    pass


class Mated(Exception):
    """The route delivered checkmate (success)."""


class Game:
    def __init__(self, S, R, L):
        self.pos = {(W, "K"): S, (W, "R"): R, (B, "K"): L}
        self.turn = W
        self.plies = 0
        self.log = []

    @property
    def S(self):
        return self.pos[(W, "K")]

    @property
    def R(self):
        return self.pos[(W, "R")]

    @property
    def L(self):
        return self.pos[(B, "K")]

    def legal(self):
        return kd.legal_moves(self.pos, self.turn)

    def play(self, piece, dest, phase):
        """Play piece -> dest for the side to move, checked against the generator."""
        want = dict(self.pos)
        want[piece] = dest
        for s in self.legal():
            if s == want:
                self.pos = s
                self.turn = B if self.turn == W else W
                self.plies += 1
                self.log.append((phase, piece, dest))
                if self.turn == B and self.mated():
                    raise Mated()
                return
        raise RouteError(f"{phase}: illegal {piece}->{dest} in {self.pos} turn {self.turn}")

    def lone_options(self):
        """Non-capturing legal lone-king destinations."""
        assert self.turn == B
        out = []
        for s in self.legal():
            if (W, "R") in s:
                out.append(s[(B, "K")])
        return out

    def mated(self):
        return kd.in_check(self.pos, self.turn) and not self.legal()


# ---------------------------------------------------------------- route phases

ZONE = [(7, 7), (6, 7), (5, 7)]          # rook home squares on the top rank
REGION = {(x, y) for x in range(5) for y in range(7)}   # lone king's working region R0


def rook_attacks(R, S, L):
    occ = {S, L, R}
    return kd.attacked_squares("R", R, occ)


def lone_step_towards(g, target, region):
    """Lone king: BFS one step towards target inside region (avoiding S's neighbourhood);
    falls back to any non-capturing legal move."""
    opts = g.lone_options()
    if not opts:
        raise RouteError(f"lone king has no non-capturing move: {g.pos}")
    S = g.S
    allowed = safe_region(g) if g.R in PARTNER else {q for q in region if dinf(q, S) >= 2 and q != g.R}
    # BFS from target backwards over allowed squares
    dist = {target: 0} if target in allowed else {}
    dq = deque(dist)
    while dq:
        q = dq.popleft()
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                n = (q[0] + dx, q[1] + dy)
                if n != q and n in allowed and n not in dist:
                    dist[n] = dist[q] + 1
                    dq.append(n)
    best = sorted(opts, key=lambda q: (dist.get(q, 99), q))
    return best[0]


def phase1_candidates(R):
    """Explicit rook routes to the zone, in the fixed order the route tries them."""
    rx, ry = R
    out = []
    if ry == 7:
        out += [[(x, 7)] for x in (7, 6, 5)]                       # P1b: along rank 8
    elif rx >= 5:
        out += [[(rx, 7)]]                                          # P1c: up the file
    else:
        out += [[(x, ry), (x, 7)] for x in (7, 6, 5)]               # P1d: across, then up
        out += [[(rx, 7), (x, 7)] for x in (7, 6, 5)]               #      up, then across
    ydet = 1 if ry == 0 else 0
    out += [[(rx, ydet), (7, ydet), (7, 7)]]                        # P1e: detour
    return out


STATS = {}


def phase1_rook_home(g):
    """Rook to the top-rank zone (files f-h) by the first explicit route that works:
    every rook move legal, and after each one the lone king has a non-capturing move
    (or is mated). Lone replies: one BFS step towards T inside R0."""
    if g.R in ZONE:
        STATS["P1a"] = STATS.get("P1a", 0) + 1
        return
    for k, seq in enumerate(phase1_candidates(g.R)):
        h = clone(g)
        try:
            for c in seq:
                h.play((W, "R"), c, "P1-rook")
                if not h.lone_options():
                    raise RouteError("no reply")
                h.play((B, "K"), lone_step_towards(h, (h.S[0], h.S[1] - 2), REGION), "P1-lone")
        except Mated:
            pass
        except RouteError:
            continue
        name = "P1e" if k == len(phase1_candidates(g.R)) - 1 else f"P1-{len(seq)}"
        STATS[name] = STATS.get(name, 0) + 1
        for c in seq:  # replay on the real game (raises Mated on mate)
            g.play((W, "R"), c, "P1-rook")
            g.play((B, "K"), lone_step_towards(g, (g.S[0], g.S[1] - 2), REGION), "P1-lone")
        return
    raise RouteError(f"P1: no rook route {g.pos}")


PARTNER = {(7, 7): (6, 7), (6, 7): (7, 7), (5, 7): (6, 7)}


def safe_region(g):
    """F: squares on ranks 1-7 attacked by the rook neither on its square nor on its tempo
    partner (both on rank 8), and not adjacent to S."""
    R = g.R
    bad = set()
    for r in (R, PARTNER.get(R, R)):
        bad |= {(r[0], y) for y in range(8)} | {(x, 7) for x in range(8)}
    return {(x, y) for x in range(8) for y in range(7)
            if (x, y) not in bad and dinf((x, y), g.S) >= 2}


def lone_connected_to_target(g):
    """Is L connected to T = S-(0,2) through R0 minus N1(S) (L itself may lie outside)?"""
    S, L = g.S, g.L
    T = (S[0], S[1] - 2)
    allowed = safe_region(g)
    if T not in allowed:
        return False
    seen = {L}
    dq = deque([L])
    while dq:
        q = dq.popleft()
        if q == T:
            return True
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                n = (q[0] + dx, q[1] + dy)
                if n in allowed and n not in seen:
                    seen.add(n)
                    dq.append(n)
    return False


def rook_tempo(g, phase):
    """Rook moves along the top rank inside the zone, never onto a king."""
    rx, _ = g.R
    for c in [PARTNER[g.R]] if g.R in PARTNER else [(x, 7) for x in (7, 6, 5) if x != rx]:
        try_g = clone(g)
        try:
            try_g.play((W, "R"), c, phase)
            if not try_g.lone_options():
                continue
        except Mated:
            pass
        except RouteError:
            continue
        g.play((W, "R"), c, phase)
        return
    raise RouteError(f"{phase}: no rook tempo {g.pos}")


def phase2_lone_walk(g):
    """Lone king walks to T = S - (0,2) inside R0 while the rook makes tempo moves."""
    target = (g.S[0], g.S[1] - 2)
    for _ in range(40):
        if g.L == target:
            return
        rook_tempo(g, "P2-tempo")
        g.play((B, "K"), lone_step_towards(g, target, REGION), "P2-lone")
    raise RouteError(f"P2: lone king did not reach {target}: {g.pos}")


def phase3_escort(g):
    """Escort down column a = sx. Entry: strong to move, L = S - (0,2)."""
    a = g.S[0]
    if g.L[1] > 0:
        rook_tempo(g, "P3-tempo")            # now lone to move, S - L = (0,2)
        while g.L[1] > 0:
            g.play((B, "K"), (a, g.L[1] - 1), "P3-lone")
            g.play((W, "K"), (a, g.S[1] - 1), "P3-strong")
        # lone to move, L = (a,0), S = (a,2): shuttle out, tempo, back
        side = (a + 1, 0) if a + 1 <= 4 else (a - 1, 0)
        g.play((B, "K"), side, "P4-shuttle")
        rook_tempo(g, "P4-tempo")
        g.play((B, "K"), (a, 0), "P4-back")
    # strong to move, L = (a,0), S = (a,2): the rook mates down its file
    rx, _ = g.R
    g.play((W, "R"), (rx, 0), "P5-mate")
    raise RouteError(f"P5: not mate {g.pos}")


def clone(g):
    h = Game.__new__(Game)
    h.pos = dict(g.pos)
    h.turn = g.turn
    h.plies = g.plies
    h.log = list(g.log)
    return h


ROUTE_GAME = [None]


def route(S, R, L):
    S, R, L = normalise(S, R, L)
    g = Game(S, R, L)
    ROUTE_GAME[0] = g
    phase1_rook_home(g)
    if not lone_connected_to_target(g):
        STATS["INV-not-connected"] = STATS.get("INV-not-connected", 0) + 1
    phase2_lone_walk(g)
    phase3_escort(g)
    return g


def strong_to_move_states():
    for S in kd.SQUARES:
        for R in kd.SQUARES:
            if R == S:
                continue
            for L in kd.SQUARES:
                if L in (S, R):
                    continue
                pos = {(W, "K"): S, (W, "R"): R, (B, "K"): L}
                if kd.in_check(pos, B):
                    continue  # the side not to move (Black) must not be in check
                yield S, R, L


def main(limit_examples=8):
    total = ok = 0
    fails = {}
    longest = 0
    for S, R, L in strong_to_move_states():
        total += 1
        g = None
        try:
            g = route(S, R, L)
        except Mated:
            ok += 1
            longest = max(longest, ROUTE_GAME[0].plies)
            continue
        except RouteError as e:
            key = str(e).split(":")[0]
            fails.setdefault(key, []).append((S, R, L, str(e)))
    print(f"strong_to_move_states: {total}")
    print(f"route_reaches_mate: {ok}")
    print(f"longest_route_plies: {longest}")
    print(f"phase1_rule_counts: {dict(sorted(STATS.items()))}")
    for k, v in sorted(fails.items(), key=lambda kv: -len(kv[1])):
        print(f"FAIL {k}: {len(v)}")
        for ex in v[:limit_examples]:
            print("   ", ex[:3])
    return 0 if ok == total else 1


if __name__ == "__main__":
    sys.exit(main())
