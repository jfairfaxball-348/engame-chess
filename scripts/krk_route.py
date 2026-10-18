#!/usr/bin/env python3
"""Strategy simulator for EC-C008 (K+R vs K, strong side to move, is never dead). Route v2 (S018).

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

def phase1_candidates(R):
    """Explicit rook routes to h8, in the fixed order the route tries them."""
    rx, ry = R
    out = []
    if ry == 7 or rx == 7:
        out.append([(7, 7)])                                   # P1-direct
    out.append([(7, ry), (7, 7)])                              # P1-HV: across, then up
    out.append([(rx, 7), (7, 7)])                              # P1-VH: up, then across
    y0 = 1 if ry == 0 else 0
    out.append([(rx, y0), (7, y0), (7, 7)])                    # P1-detour
    return [[c for c in seq if c != R] for seq in out]


STATS = {}
NAMES = ["P1-direct", "P1-HV", "P1-VH", "P1-detour"]


def p1_lone_reply(g):
    """Lone reply during P1: prefer squares of G (files a-f, ranks 1-7) not adjacent to S."""
    opts = g.lone_options()
    if not opts:
        raise RouteError("no reply")
    G = region(g, "G")
    return sorted(opts, key=lambda q: (q not in G, q))[0]


def phase1_rook_home(g):
    """Rook to h8 by the first explicit route that works (every rook move legal; after each,
    the lone king has a non-capturing move, or is mated)."""
    if g.R == (7, 7):
        STATS["P1-home"] = STATS.get("P1-home", 0) + 1
        return
    cands = phase1_candidates(g.R)
    if g.R[1] != 7 and g.R[0] != 7:
        names = NAMES[1:]
    else:
        names = NAMES
    for name, seq in zip(names, cands):
        h = clone(g)
        try:
            for c in seq:
                h.play((W, "R"), c, "P1-rook")
                h.play((B, "K"), p1_lone_reply(h), "P1-lone")
        except Mated:
            pass
        except RouteError:
            continue
        STATS[name] = STATS.get(name, 0) + 1
        for c in seq:
            g.play((W, "R"), c, "P1-rook")
            g.play((B, "K"), p1_lone_reply(g), "P1-lone")
        return
    raise RouteError(f"P1: no rook route {g.pos}")


def region(g, kind):
    """G: files a-f, ranks 1-7 (tempo h8<->g8).  H: files a-g, ranks 1-6 (tempo h8<->h7).
    Both minus the strong king's neighbourhood."""
    if kind == "G":
        sq = {(x, y) for x in range(6) for y in range(7)}
    else:
        sq = {(x, y) for x in range(7) for y in range(6)}
    return {q for q in sq if dinf(q, g.S) >= 2}


TEMPO = {"G": {(7, 7): (6, 7), (6, 7): (7, 7)}, "H": {(7, 7): (7, 6), (7, 6): (7, 7)}}


def tempo(g, kind, phase):
    g.play((W, "R"), TEMPO[kind][g.R], phase)


def walk(g, kind, target):
    """Lemma W: strong tempo inside the pair, lone king one BFS step inside the region."""
    for _ in range(40):
        if g.L == target:
            return
        F = region(g, kind)
        if target not in F:
            raise RouteError(f"W: target outside region {g.pos}")
        dist = {target: 0}
        dq = deque([target])
        while dq:
            q = dq.popleft()
            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    n = (q[0] + dx, q[1] + dy)
                    if n in F and n not in dist:
                        dist[n] = dist[q] + 1
                        dq.append(n)
        tempo(g, kind, "P2-tempo")
        nxt = sorted((q for q in g.lone_options() if q in dist), key=lambda q: (dist[q], q))
        if not nxt:
            raise RouteError(f"W: lone king not connected to T {g.pos}")
        g.play((B, "K"), nxt[0], "P2-lone")
    raise RouteError(f"W: walk too long {g.pos}")


def phase2(g):
    """Settle (four cases) and walk to T = S - (0,2). Returns the tempo pair used."""
    T = (g.S[0], g.S[1] - 2)
    L = g.L
    if L in region(g, "G"):
        kind = "G"; STATS["P2-G"] = STATS.get("P2-G", 0) + 1
    elif L[0] == 6 and L[1] <= 5:
        kind = "H"; STATS["P2-H"] = STATS.get("P2-H", 0) + 1
    elif L == (6, 6):
        STATS["P2-g7"] = STATS.get("P2-g7", 0) + 1
        g.play((W, "R"), (6, 7), "P2-g7-check")
        g.play((B, "K"), (5, 5), "P2-g7-Kf6")
        kind = "G"
    elif L[1] == 7:
        STATS["P2-rank8"] = STATS.get("P2-rank8", 0) + 1
        g.play((W, "R"), (6, 7), "P2-rank8-tempo")
        g.play((B, "K"), (L[0], 6), "P2-rank8-down")
        kind = "G"
    else:
        raise RouteError(f"P2: unclassified lone king {g.pos}")
    if g.L != T:
        walk(g, kind, T)
    return kind


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
    kind = phase2(g)
    escort(g, kind)
    return g


def escort(g, kind):
    """Lemma E: from strong to move, L = S - (0,2); march down, shuttle, mate."""
    a = g.S[0]
    if g.L[1] > 0:
        tempo(g, kind, "P3-tempo")
        while g.L[1] > 0:
            g.play((B, "K"), (a, g.L[1] - 1), "P3-lone")
            g.play((W, "K"), (a, g.S[1] - 1), "P3-strong")
        g.play((B, "K"), (a + 1, 0), "P4-shuttle")
        tempo(g, kind, "P4-tempo")
        g.play((B, "K"), (a, 0), "P4-back")
    g.play((W, "R"), (g.R[0], 0), "P5-mate")
    raise RouteError(f"P5: not mate {g.pos}")


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
