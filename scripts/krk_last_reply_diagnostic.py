"""Local diagnostics for the analytic last-defender-move conjecture.

No tablebase, engine, retrograde graph or stored position values. This compares
a proposed coordinate formula with the repository's own move generator in
small selected families and a deterministic sample. It is not a proof.
"""
import json
import random

from krk_diagnostic import B, W, in_check, legal_moves


def horizontal(sk, rook, wk):
    x, y = wk
    return (
        rook[1] == y
        and ((y == 0 and sk[1] == 2) or (y == 7 and sk[1] == 5))
        and abs(rook[0] - x) >= 2
        and (sk[0] <= 1 if x == 0 else sk[0] >= 6 if x == 7 else sk[0] == x)
    )


def swap(s):
    return s[1], s[0]


def terminal(sk, rook, wk):
    return horizontal(sk, rook, wk) or horizontal(swap(sk), swap(rook), swap(wk))


def immediate(pos):
    if (W, "R") not in pos:
        return False
    sk, wk = pos[W, "K"], pos[B, "K"]
    # At most two destinations are potential mating squares; the local move
    # generator checks the actual clear path and king safety independently.
    return any(terminal(nxt[W, "K"], nxt[W, "R"], wk)
               for nxt in legal_moves(pos, W))


def horizontal_last_reply(sk, rook, wk):
    x, y = wk
    if not (((y == 0 and sk[1] == 2) or (y == 7 and sk[1] == 5))
            and rook[1] != y):
        return False
    sx, rx = sk[0], rook[0]
    if x == 0:
        return sx == 1 and rx >= 3
    if x == 7:
        return sx == 6 and rx <= 4
    toward_right = (sx == x + 1 or (x == 6 and sx == 6)) and rx == x - 1
    toward_left = (sx == x - 1 or (x == 1 and sx == 1)) and rx == x + 1
    return toward_right or toward_left


def last_reply(sk, rook, wk):
    safe = (max(abs(rook[i] - wk[i]) for i in (0, 1)) >= 2
            or max(abs(sk[i] - rook[i]) for i in (0, 1)) == 1)
    return safe and (horizontal_last_reply(sk, rook, wk)
                     or horizontal_last_reply(swap(sk), swap(rook), swap(wk)))


def run():
    samples = []
    # Canonical edge and inward-king families, including both corner offsets.
    for sx in range(8):
        for wx in range(8):
            for rx in range(8):
                for ry in range(8):
                    samples.append(((sx, 2), (rx, ry), (wx, 0)))
    rng = random.Random(20261026)
    squares = [(x, y) for x in range(8) for y in range(8)]
    samples.extend(tuple(rng.sample(squares, 3)) for _ in range(2000))
    checked = positive = 0
    mismatches = []
    for sk, rook, wk in samples:
        if len({sk, rook, wk}) != 3 or max(abs(sk[i] - wk[i]) for i in (0, 1)) < 2:
            continue
        pos = {(W, "K"): sk, (W, "R"): rook, (B, "K"): wk}
        replies = legal_moves(pos, B)
        if not replies and in_check(pos, B):
            continue  # terminal mate is a separate clause
        observed = bool(replies) and all(immediate(nxt) for nxt in replies)
        predicted = last_reply(sk, rook, wk)
        checked += 1
        positive += observed
        if observed != predicted or (observed and len(replies) != 1):
            mismatches.append(dict(sk=sk, rook=rook, wk=wk, predicted=predicted,
                                   observed=observed, reply_count=len(replies)))
    result = dict(diagnostic_only=True, checked=checked, positive=positive,
                  mismatches=mismatches[:12], mismatch_count=len(mismatches))
    print(json.dumps(result, indent=2))
    return not mismatches


if __name__ == "__main__":
    raise SystemExit(0 if run() else 1)
