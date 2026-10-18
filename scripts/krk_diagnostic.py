#!/usr/bin/env python3
"""Exhaustive K+R vs K diagnostic for EC-C007 (which K+R vs K positions are dead?).

DIAGNOSTIC SUPPLEMENT ONLY: this is NOT a proof and NOT a tablebase. It reads no
external data and stores no evaluations beyond this run. Moves are generated directly
from FIDE 2023 Articles 3.1, 3.3 (rook: along the file or rank) and 3.5 (no passing
over pieces; rays are walked square by square), 3.8.1 (king: adjoining square) and 3.9
(check). Castling is not generated: it only adds strong-side moves, so it can only make
more positions live; see proofs/EC-C007_KRK_LIVE.md for why the characterisation is
insensitive to it.

"Live" means some finite series of legal moves (both sides cooperating) reaches a
checkmate. It is computed as a backward-reachability fixpoint over this script's own
move graph on K+R vs K and K vs K states. The conjectured characterisation of
EC-C007 is then compared with the computed dead set, state by state.

Conjecture (EC-C007), for a legal state (side not to move is not in check):
  dead  <=>  weak side to move, not checkmate, and every legal move captures the rook
             (vacuously true in stalemate).
"""
import sys
import time
from collections import deque

N = 8
SQUARES = [(x, y) for x in range(N) for y in range(N)]
KING_STEPS = [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)]
LINES = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DIAGONALS = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
W, B = "W", "B"
OTHER = {W: B, B: W}


def on_board(x, y):
    return 0 <= x < N and 0 <= y < N


def attacked_squares(kind, sq, occupied):
    """Squares a piece of `kind` on `sq` could capture on (Art. 3.1.2), ignoring self-check.
    kind "R" is the rook; kind "B" (bishop) exists only for the mutation test."""
    x, y = sq
    out = set()
    if kind == "K":
        for dx, dy in KING_STEPS:
            if on_board(x + dx, y + dy):
                out.add((x + dx, y + dy))
        return out
    dirs = LINES if kind == "R" else DIAGONALS
    for dx, dy in dirs:
        cx, cy = x + dx, y + dy
        while on_board(cx, cy):
            out.add((cx, cy))
            if (cx, cy) in occupied:
                break  # Art. 3.5
            cx, cy = cx + dx, cy + dy
    return out


def in_check(pos, colour):
    occupied = set(pos.values())
    king = pos[(colour, "K")]
    return any(king in attacked_squares(kind, sq, occupied)
               for (c, kind), sq in pos.items() if c != colour)


def legal_moves(pos, to_move):
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
                continue  # 1.4.1
            nxt = dict(pos)
            if victim is not None:
                del nxt[victim]
            nxt[(c, kind)] = dest
            if in_check(nxt, to_move):
                continue  # 3.9.2
            out.append(nxt)
    return out


def key(pos, t):
    return (frozenset(pos.items()), t)


def run(strong=W, piece="R"):
    """Build the legal-state graph for one orientation, compute the live set, and compare
    it with the conjecture. Returns a dict of counts plus example mismatches."""
    start = time.time()
    weak = OTHER[strong]
    states = {}          # key -> (pos, t)
    succ = {}            # key -> list of successor keys
    # all K+R vs K placements
    for sk in SQUARES:
        for rs in SQUARES:
            if rs == sk:
                continue
            for wk in SQUARES:
                if wk in (sk, rs):
                    continue
                for t in (W, B):
                    pos = {(strong, "K"): sk, (strong, piece): rs, (weak, "K"): wk}
                    if in_check(pos, OTHER[t]):
                        continue
                    states[key(pos, t)] = (pos, t)
    krk_keys = list(states)
    # K vs K states reachable by captures are added lazily
    frontier = list(states)
    while frontier:
        k = frontier.pop()
        if k in succ:
            continue
        pos, t = states[k]
        lst = []
        for s in legal_moves(pos, t):
            sk_ = key(s, OTHER[t])
            if sk_ not in states:
                states[sk_] = (s, OTHER[t])
                frontier.append(sk_)
            lst.append(sk_)
        succ[k] = lst
    # mates and backward reachability
    preds = {k: [] for k in states}
    for k, lst in succ.items():
        for s in lst:
            preds[s].append(k)
    mate = {k for k, (pos, t) in states.items() if not succ[k] and in_check(pos, t)}
    live = set(mate)
    dq = deque(mate)
    while dq:
        k = dq.popleft()
        for p in preds[k]:
            if p not in live:
                live.add(p)
                dq.append(p)
    r = dict(legal_krk_states=len(krk_keys), kk_states=len(states) - len(krk_keys),
             checkmates=0, stalemates=0, checks_of_lone_king=0, forced_rook_captures=0,
             dead_states=0, dead_strong_to_move=0, dead_weak_to_move=0,
             mismatches=0, kk_live=0)
    examples = []
    rook_key = (strong, piece)
    for k in krk_keys:
        pos, t = states[k]
        s = succ[k]
        if k in mate:
            r["checkmates"] += 1
        elif not s:
            r["stalemates"] += 1
        if t == weak and in_check(pos, weak):
            r["checks_of_lone_king"] += 1
        all_capture = all(rook_key not in states[x][0] for x in s)
        if t == weak and s and all_capture:
            r["forced_rook_captures"] += 1
        dead = k not in live
        if dead:
            r["dead_states"] += 1
            r["dead_strong_to_move" if t == strong else "dead_weak_to_move"] += 1
        predicted = (t == weak) and (k not in mate) and all_capture
        if dead != predicted:
            r["mismatches"] += 1
            if len(examples) < 5:
                examples.append((pos, t, "dead" if dead else "live"))
    krk_set = set(krk_keys)
    for k in states:
        if k not in krk_set and k in live:
            r["kk_live"] += 1
    r["seconds"] = round(time.time() - start, 1)
    return r, examples


EXPECTED_ZERO = ["mismatches", "dead_strong_to_move", "kk_live"]


def main():
    ok = True
    for strong in (W, B):
        r, ex = run(strong)
        print(f"== K+R vs K, strong side {strong} ==")
        for k, v in r.items():
            print(f"{k}: {v}")
        for e in ex:
            print("  example:", e)
        if any(r[k] != 0 for k in EXPECTED_ZERO):
            ok = False
    m, ex = run(W, piece="B")
    print("== mutation: rook replaced by a bishop (strong side W) ==")
    print(f"mismatches: {m['mismatches']}  dead_states: {m['dead_states']}  checkmates: {m['checkmates']}")
    if m["mismatches"] == 0:
        ok = False
        print("mutation not detected")
    print("KRK DIAGNOSTIC PASSED (supplementary evidence, not a proof)" if ok
          else "KRK DIAGNOSTIC FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
