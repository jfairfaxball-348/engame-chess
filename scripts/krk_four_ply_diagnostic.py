"""Selected-family diagnostics for the next weak-turn geometric frontier.

No tablebase, engine, retrograde graph, or stored position values. The checked
three-ply coordinate predicate is evaluated at local legal replies to discover
four-ply boundary cases. These observations are not theorem evidence.
"""
from collections import Counter
import argparse
import json
import random

from krk_diagnostic import B, W, legal_moves
from krk_last_reply_diagnostic import horizontal, last_reply, swap

SQUARES = [(x, y) for x in range(8) for y in range(8)]


def distance(a, b):
    return max(abs(a[i] - b[i]) for i in (0, 1))


def neighbours(s):
    return [(x, y) for x in range(max(0, s[0] - 1), min(8, s[0] + 2))
            for y in range(max(0, s[1] - 1), min(8, s[1] + 2)) if (x, y) != s]


def sees(a, b, sk, wk):
    if a == b or (a[0] != b[0] and a[1] != b[1]):
        return False
    def between(s):
        if a[0] == b[0]:
            return s[0] == a[0] and min(a[1], b[1]) < s[1] < max(a[1], b[1])
        return s[1] == a[1] and min(a[0], b[0]) < s[0] < max(a[0], b[0])
    return not between(sk) and not between(wk)


def mate_now(sk, rook, wk):
    rank = (rook[0], wk[1])
    file = (wk[0], rook[1])
    return ((horizontal(sk, rank, wk) and sees(rook, rank, sk, wk)) or
            (horizontal(swap(sk), swap(file), swap(wk)) and sees(rook, file, sk, wk)))


def three(sk, rook, wk):
    if mate_now(sk, rook, wk):
        return True
    if any(t != rook and distance(t, wk) >= 2 and last_reply(t, rook, wk)
           for t in neighbours(sk)):
        return True
    return any(t != sk and t != wk and sees(rook, t, sk, wk) and last_reply(sk, t, wk)
               for t in SQUARES)


def run():
    rng = random.Random(20261027)
    cases = []
    # Both the edge and first inward band, with all king offsets represented.
    for wy in (0, 1):
        for wx in range(8):
            for sy in range(5):
                for sx in range(8):
                    for _ in range(12):
                        cases.append(((sx, sy), rng.choice(SQUARES), (wx, wy)))
    checked = positives = missed_prison = 0
    groups = Counter()
    examples = {}
    for sk, rook, wk in cases:
        if len({sk, rook, wk}) != 3 or distance(sk, wk) < 2:
            continue
        pos = {(W, "K"): sk, (W, "R"): rook, (B, "K"): wk}
        replies = legal_moves(pos, B)
        if not replies:
            continue  # terminal cases remain separate
        checked += 1
        observed = all((W, "R") in p and three(p[W, "K"], p[W, "R"], p[B, "K"])
                       for p in replies)
        if not observed:
            continue
        positives += 1
        edge_prison = all(min(*p[B, "K"], 7-p[B, "K"][0], 7-p[B, "K"][1]) == 0
                          for p in replies)
        missed_prison += not edge_prison
        if not last_reply(sk, rook, wk):
            group = (wk[1], sk[1], rook[1], len(replies))
            groups[group] += 1
            examples.setdefault(group, dict(sk=sk, rook=rook, wk=wk,
                                           replies=[p[B, "K"] for p in replies]))
    print(json.dumps(dict(diagnostic_only=True, checked=checked, positive=positives,
                         edge_prison_violations=missed_prison,
                         new_region_examples=[dict(group=g, count=n, example=examples[g])
                                              for g, n in groups.most_common(12)]), indent=2))


def run_interior():
    checked = positive = 0
    examples = []
    for wk in [(1, 1), (2, 1), (3, 1)]:
        for sk in SQUARES:
            for rook in SQUARES:
                if len({wk, sk, rook}) < 3 or distance(sk, wk) < 2:
                    continue
                pos = {(W, "K"): sk, (W, "R"): rook, (B, "K"): wk}
                replies = legal_moves(pos, B)
                if not replies:
                    continue
                checked += 1
                if all((W, "R") in p and three(p[W, "K"], p[W, "R"], p[B, "K"])
                       for p in replies):
                    positive += 1
                    if len(examples) < 12:
                        examples.append(dict(sk=sk, rook=rook, wk=wk))
    print(json.dumps(dict(diagnostic_only=True, checked=checked,
                         interior_weak_four_positive=positive, examples=examples), indent=2))


def edge_candidate(sk, rook, wk):
    """Unproved bottom-edge four-ply formula, conditional on a nonterminal root."""
    x, y = wk
    assert y == 0
    if x >= 4:
        sk, rook, wk = (7-sk[0], sk[1]), (7-rook[0], rook[1]), (7-x, y)
        x = wk[0]
    rx, ry = rook
    sx, sy = sk
    if x >= 2:
        return last_reply(sk, rook, wk) or (sk == (x, 2) and ry >= 3)
    if x == 1:
        return ((sk == (0, 2) and rx == 2 and ry >= 2) or
                (sk == (1, 2) and (ry >= 3 or (ry == 2 and rx >= 2) or
                                   (ry == 1 and rx in (2, 3)))) or
                (sk == (2, 2) and ((rx == 0 and ry >= 2) or
                                   (rx >= 3 and rook != (3, 1)))))
    return ((sk == (0, 2) and (ry >= 2 or rx == 2)) or
            (sk == (2, 0) and (rx >= 2 or ry == 2)) or
            (sk == (1, 2) and ry >= 1) or (sk == (2, 1) and rx >= 1) or
            (sk == (2, 2) and ((rx >= 3 and ry >= 3) or (rx == 0 and ry >= 2) or
                               (ry == 0 and rx >= 2) or rook in ((1, 2), (2, 1)))) or
            (sy == 3 and sx <= 2 and rook == (2, 1)) or
            (sx == 3 and sy <= 2 and rook == (1, 2)))


def run_edges():
    checked = positive = 0
    mismatches = []
    for wx in (0, 1, 2, 3):
        wk = (wx, 0)
        for sk in SQUARES:
            for rook in SQUARES:
                if len({wk, sk, rook}) < 3 or distance(sk, wk) < 2:
                    continue
                replies = legal_moves({(W, "K"): sk, (W, "R"): rook, (B, "K"): wk}, B)
                if not replies:
                    continue  # the conjecture explicitly excludes terminal roots
                observed = all((W, "R") in p and three(p[W, "K"], p[W, "R"], p[B, "K"])
                               for p in replies)
                predicted = edge_candidate(sk, rook, wk)
                checked += 1
                positive += observed
                if observed != predicted:
                    mismatches.append(dict(sk=sk, rook=rook, wk=wk, observed=observed,
                                           predicted=predicted))
    print(json.dumps(dict(diagnostic_only=True, conjecture="edge four-ply coordinate formula",
                         checked=checked, positive=positive, mismatch_count=len(mismatches),
                         examples=mismatches[:12]), indent=2))
    return not mismatches


def three_middle_candidate(sk, rook, wk):
    x, y = wk
    assert y == 0 and 2 <= x <= 5
    sx, sy = sk
    rx, ry = rook
    return ((sk == (x, 2) and ry != 0 and abs(rx-x) >= 2) or
            (ry >= 2 and rx == x-1 and distance(sk, (x+1, 2)) == 1) or
            (ry >= 2 and rx == x+1 and distance(sk, (x-1, 2)) == 1) or
            (sk == (x+1, 2) and (rx == x-1 or ry >= 3 or (ry == 2 and rx < sx))) or
            (sk == (x-1, 2) and (rx == x+1 or ry >= 3 or (ry == 2 and sx < rx))))


def run_middle_three():
    checked = 0
    mismatches = []
    for x in (2, 3, 4, 5):
        wk = (x, 0)
        for sk in SQUARES:
            for rook in SQUARES:
                if len({wk, sk, rook}) < 3 or distance(sk, wk) < 2:
                    continue
                checked += 1
                predicted = three_middle_candidate(sk, rook, wk)
                observed = three(sk, rook, wk)
                if observed != predicted:
                    mismatches.append(dict(sk=sk, rook=rook, wk=wk, observed=observed,
                                           predicted=predicted))
    print(json.dumps(dict(diagnostic_only=True, conjecture="central-edge three-ply expansion",
                         checked=checked, mismatch_count=len(mismatches), examples=mismatches[:12]), indent=2))
    return not mismatches


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--interior", action="store_true", help="check three selected inward-band families")
    parser.add_argument("--edge-formula", action="store_true", help="test the unproved coordinate conjecture")
    parser.add_argument("--middle-three", action="store_true", help="test the unproved central three-ply expansion")
    args = parser.parse_args()
    if args.middle_three:
        raise SystemExit(0 if run_middle_three() else 1)
    if args.edge_formula:
        raise SystemExit(0 if run_edges() else 1)
    run_interior() if args.interior else run()
