#!/usr/bin/env python3
"""Local adversarial checks for S026's opposed-kings checking phase.
No class graph, retrograde fixpoint, engine or external table is used.
For a fixed small set of configurations, test every reply for two defending plies.
The proof is symbolic; this diagnostic only searches for errors in its stated domain.
"""
import json
import krk_diagnostic as kd


def distance(a, b):
    return max(abs(a[0]-b[0]), abs(a[1]-b[1]))


def position(s, r, w, strong):
    return {(strong, 'K'): s, (strong, 'R'): r, (kd.OTHER[strong], 'K'): w}


def move(pos, side, piece, dest):
    out = dict(pos)
    out[piece] = dest
    assert out in kd.legal_moves(pos, side), (pos, side, piece, dest)
    return out


def phase(sx, sy, rx, ry, strong):
    weak = kd.OTHER[strong]
    s, w, old_r = (sx, sy), (sx, sy+2), (rx, ry)
    assert abs(rx-sx) >= 4 and ry != w[1]
    pos = position(s, old_r, w, strong)
    target = (rx, w[1])
    check = move(pos, strong, (strong, 'R'), target)
    assert kd.in_check(check, weak)
    replies = kd.legal_moves(check, weak)
    if w[1] == 7:
        assert not replies
        return {'mate': 1, 'first_replies': 0, 'second_replies': 0}
    assert replies
    count = 0
    for reply in replies:
        assert reply[(weak, 'K')][1] == w[1]+1
        assert (strong, 'R') in reply
        up = (sx, sy+1)
        approached = move(reply, strong, (strong, 'K'), up)
        second = kd.legal_moves(approached, weak)
        assert second, ('stalemate', approached)
        for nxt in second:
            assert nxt[(strong, 'R')] == target
            assert nxt[(weak, 'K')][1] > w[1]
            assert distance(nxt[(weak, 'K')], target) >= 2
            assert up[1] < target[1] < nxt[(weak, 'K')][1]
            count += 1
    return {'mate': 0, 'first_replies': len(replies), 'second_replies': count}


def run():
    samples = [(0,0,7,7),(1,1,7,0),(2,2,7,0),(3,3,7,0),
               (4,0,0,7),(5,1,0,0),(6,2,0,0),(7,4,0,0),
               (0,5,7,0),(3,5,7,0),(4,5,0,0),(7,5,0,0)]
    totals = {'configurations': 0, 'mate': 0, 'first_replies': 0, 'second_replies': 0}
    for strong in [kd.W, kd.B]:
        for sample in samples:
            stats = phase(*sample, strong)
            totals['configurations'] += 1
            for key, val in stats.items(): totals[key] += val
    # Gap two is inadequate for the four-ply phase: the second reply can capture.
    p = position((0,0),(2,0),(0,2),kd.W)
    p = move(p,kd.W,(kd.W,'R'),(2,2))
    p = move(p,kd.B,(kd.B,'K'),(1,3))
    p = move(p,kd.W,(kd.W,'K'),(0,1))
    cap = dict(p); del cap[(kd.W,'R')]; cap[(kd.B,'K')] = (2,2)
    assert cap in kd.legal_moves(p,kd.B)
    # Gap three preserves material, but the rook may be en prise after two replies.
    p = position((0,0),(3,0),(0,2),kd.W)
    for side,piece,dest in [(kd.W,(kd.W,'R'),(3,2)),(kd.B,(kd.B,'K'),(1,3)),
                            (kd.W,(kd.W,'K'),(0,1)),(kd.B,(kd.B,'K'),(2,3))]:
        p = move(p,side,piece,dest)
    assert distance(p[(kd.W,'R')],p[(kd.B,'K')]) == 1
    return {'supplementary_only': True, **totals,
            'gap_two_capture_control': True, 'gap_three_hanging_rook_control': True}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
