"""Selected local phase trees only; no class graph, oracle or game-value search.

Only legal_moves from the old ray model is imported; its run() is NEVER called.
Every edge is additionally checked by the independent direct KRK checker below.
No result here is a Lean certificate or an admitted full initial history.
"""
import datetime
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import krk_diagnostic as kd


def independent_edge(p, q, side):
    if set(p) != set(q):
        return False
    changed = [k for k in p if p[k] != q[k]]
    if len(changed) != 1 or changed[0][0] != side:
        return False
    key = changed[0]
    src, dst = p[key], q[key]
    if not all(0 <= z <= 7 for z in dst) or len(set(q.values())) != 3:
        return False
    dx, dy = dst[0] - src[0], dst[1] - src[1]
    if key[1] == 'K':
        if max(abs(dx), abs(dy)) != 1:
            return False
    else:
        if (dx == 0) == (dy == 0):
            return False
        vx, vy = (dx > 0) - (dx < 0), (dy > 0) - (dy < 0)
        x, y = src[0] + vx, src[1] + vy
        while (x, y) != dst:
            if (x, y) in p.values():
                return False
            x, y = x + vx, y + vy
    sk, rook, wk = q[('W', 'K')], q[('W', 'R')], q[('B', 'K')]
    if max(abs(sk[0]-wk[0]), abs(sk[1]-wk[1])) < 2:
        return False
    if side == 'B':
        # The strong king is the only possible intervening blocker.
        if rook[0] == wk[0]:
            if not (sk[0] == rook[0] and min(rook[1], wk[1]) < sk[1] < max(rook[1], wk[1])):
                return False
        if rook[1] == wk[1]:
            if not (sk[1] == rook[1] and min(rook[0], wk[0]) < sk[0] < max(rook[0], wk[0])):
                return False
    return True


def advance(p, side, kind, target):
    q = dict(p)
    q[(side, kind)] = target
    assert q in kd.legal_moves(p, side), ('illegal prescribed move', p, side, kind, target)
    assert independent_edge(p, q, side), ('independent replay failure', p, q)
    return q


def replies(p, stats):
    out = kd.legal_moves(p, 'B')
    assert out, ('stalemate', p)
    s, r = p[('W', 'K')], p[('W', 'R')]
    assert max(abs(s[0]-r[0]), abs(s[1]-r[1])) == 1
    for q in out:
        assert set(q) == set(p), ('capture', p, q)
        assert independent_edge(p, q, 'B'), ('independent weak replay failure', p, q)
    stats['weak_nodes'] += 1
    stats['weak_edges'] += len(out)
    return out


def phase(a, b, w):
    p = {('W', 'K'): (a-1, b-1), ('W', 'R'): (a, b), ('B', 'K'): w}
    stats = dict(a=a, b=b, weak=list(w), weak_nodes=0, weak_edges=0,
                 right_leaves=0, left_leaves=0, max_plies=0)
    old_e = max(7-a-4, 0) + max(7-b-4, 0)
    for p1 in replies(advance(p, 'W', 'K', (a, b-1)), stats):
        assert p1[('B', 'K')][0] > a and p1[('B', 'K')][1] > b
        for p2 in replies(advance(p1, 'W', 'R', (a+1, b)), stats):
            x, y = p2[('B', 'K')]
            assert y > b
            if x > a+1:
                stats['right_leaves'] += 1
                stats['max_plies'] = max(stats['max_plies'], 4)
                new_e = max(6-a-4, 0) + max(7-b-4, 0)
                assert 4 + 8*new_e <= 8*old_e
            else:
                assert x == a
                for p3 in replies(advance(p2, 'W', 'K', (a+1, b-1)), stats):
                    assert p3[('B', 'K')][0] < a+1 and p3[('B', 'K')][1] > b
                    for p4 in replies(advance(p3, 'W', 'K', (a+2, b-1)), stats):
                        assert p4[('B', 'K')][0] < a+1 and p4[('B', 'K')][1] > b
                        stats['left_leaves'] += 1
                        stats['max_plies'] = 8
                        new_e = max(a+1-4, 0) + max(7-b-4, 0)
                        assert 8 + 8*new_e <= 8*old_e
    return stats


def cycle():
    start = {('W', 'K'): (2, 2), ('W', 'R'): (3, 3), ('B', 'K'): (4, 4)}
    p = dict(start)
    moves = [('W','K',(3,2)), ('B','K',(4,5)), ('W','R',(4,3)), ('B','K',(3,4)),
             ('W','K',(4,2)), ('B','K',(2,4)), ('W','K',(5,2)), ('B','K',(3,4))]
    trace = []
    for reflected in (False, True):
        for side, kind, t in moves:
            target = (7-t[0], t[1]) if reflected else t
            p = advance(p, side, kind, target)
            trace.append(dict(side=side, kind=kind, target=target))
    assert p == start
    return trace


data = dict(scope='SIX disclosed local guarded-box phase trees, all weak replies for <=8 plies; supplementary only',
            results=[phase(a,b,w) for a,b,w in [(1,1,(2,2)), (2,3,(3,4)),
                     (1,6,(2,7)), (2,6,(4,7)), (1,2,(7,7)), (2,1,(6,2))]],
            width_four_cycle=cycle(), independent_direct_edge_replay=True,
            raw_initial_history='NOT ASSERTED', class_enumeration=False,
            finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            source_hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in (Path(__file__), ROOT/'scripts/krk_diagnostic.py')})
path = Path(__file__).with_name('guarded-box.json')
path.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(data, indent=2))
