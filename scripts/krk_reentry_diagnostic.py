#!/usr/bin/env python3
"""S028: selected local phase images, rank raises and failed-policy trajectories.
Supplementary error finding only. No class graph, value search or external oracle.
"""
import json
import krk_diagnostic as kd
from krk_check_phase_diagnostic import position, move, distance


def image(s, r, w):
    return (r[1] == s[1]+1 and w[1]-r[1] in (1, 2)
            and abs(w[0]-s[0]) <= 2 and abs(r[0]-s[0]) >= 4
            and distance(r, w) >= 2)


def image_replies(sx, sy, rx, ry, strong):
    weak = kd.OTHER[strong]
    p = position((sx, sy), (rx, ry), (sx, sy+2), strong)
    c = move(p, strong, (strong, 'R'), (rx, sy+2))
    first = kd.legal_moves(c, weak)
    if sy == 5:
        assert not first and kd.in_check(c, weak)
        return 0
    assert first
    count = 0
    for t in first:
        u = move(t, strong, (strong, 'K'), (sx, sy+1))
        replies = kd.legal_moves(u, weak)
        assert replies
        for v in replies:
            assert image(v[(strong, 'K')], v[(strong, 'R')], v[(weak, 'K')])
            count += 1
    return count


def rank_raise(s, r, w, strong):
    assert s[1] < r[1] and r[1]+2 <= w[1] and abs(r[0]-w[0]) >= 3
    weak = kd.OTHER[strong]
    nr = (r[0], r[1]+1)
    c = move(position(s, r, w, strong), strong, (strong, 'R'), nr)
    replies = kd.legal_moves(c, weak)
    assert replies
    for v in replies:
        assert v[(strong, 'R')] == nr
        assert s[1] < nr[1] < v[(weak, 'K')][1]
        assert distance(nr, v[(weak, 'K')]) >= 2
    assert 7-nr[1] < 7-r[1]
    return len(replies)


def rank_raise_rescue(s, r, w, strong):
    assert s[1] < r[1] and r[1]+2 <= w[1] and abs(r[0]-w[0]) >= 2
    weak = kd.OTHER[strong]
    nr = (r[0], r[1]+1)
    c = move(position(s, r, w, strong), strong, (strong, 'R'), nr)
    replies = kd.legal_moves(c, weak)
    assert replies
    rescues = second = 0
    for v in replies:
        assert (strong, 'R') in v and v[(weak, 'K')][1] > nr[1]
        if distance(nr, v[(weak, 'K')]) >= 2:
            continue
        rescues += 1
        target = (0 if v[(weak, 'K')][0] >= 4 else 7, nr[1])
        d = move(v, strong, (strong, 'R'), target)
        repair_replies = kd.legal_moves(d, weak)
        assert repair_replies
        for out in repair_replies:
            assert out[(weak, 'K')][1] > target[1]
            assert distance(target, out[(weak, 'K')]) >= 2
            second += 1
    return len(replies), rescues, second


def controls():
    # This phase image and the chase cycle are actually reached by legal moves.
    p = position((1, 0), (7, 0), (1, 2), kd.W)
    for side, piece, dest in [(kd.W, (kd.W, 'R'), (7, 2)),
                              (kd.B, (kd.B, 'K'), (1, 3)),
                              (kd.W, (kd.W, 'K'), (1, 1)),
                              (kd.B, (kd.B, 'K'), (2, 3))]:
        p = move(p, side, piece, dest)
    start = dict(p)
    assert image(p[(kd.W, 'K')], p[(kd.W, 'R')], p[(kd.B, 'K')])
    for side, piece, dest in [(kd.W, (kd.W, 'K'), (2, 1)),
                              (kd.B, (kd.B, 'K'), (1, 3)),
                              (kd.W, (kd.W, 'K'), (1, 1)),
                              (kd.B, (kd.B, 'K'), (2, 3))]:
        p = move(p, side, piece, dest)
    assert p == start  # no rank progress, no opposition on either strong turn
    # A protected inward corner-rook move can stalemate an actual phase image.
    p = position((5, 5), (0, 6), (7, 7), kd.W)
    assert image((5, 5), (0, 6), (7, 7))
    p = move(p, kd.W, (kd.W, 'R'), (6, 6))
    assert not kd.in_check(p, kd.B) and not kd.legal_moves(p, kd.B)
    # Lower-band raising permits a reply BELOW the new rook rank.
    p = position((0, 1), (4, 2), (2, 3), kd.W)
    assert image((0, 1), (4, 2), (2, 3))
    p = move(p, kd.W, (kd.W, 'R'), (4, 3))
    p = move(p, kd.B, (kd.B, 'K'), (2, 2))
    assert p[(kd.B, 'K')][1] < p[(kd.W, 'R')][1]
    # Upper-band raising with only two files of margin leaves the rook hanging.
    p = position((0, 1), (4, 2), (2, 4), kd.W)
    assert image((0, 1), (4, 2), (2, 4))
    p = move(p, kd.W, (kd.W, 'R'), (4, 3))
    p = move(p, kd.B, (kd.B, 'K'), (3, 4))
    assert distance(p[(kd.W, 'R')], p[(kd.B, 'K')]) == 1
    assert distance(p[(kd.W, 'K')], p[(kd.W, 'R')]) >= 2
    return {'legal_chase_cycle': True, 'protected_corner_stalemate': True,
            'lower_band_crossing': True, 'two_file_raise_hanging': True}


def run():
    samples = [(0, 0, 7, 7), (1, 1, 7, 0), (2, 2, 7, 0), (3, 3, 7, 0),
               (4, 0, 0, 7), (5, 1, 0, 0), (6, 2, 0, 0), (7, 4, 0, 0),
               (0, 5, 7, 0), (3, 5, 7, 0), (4, 5, 0, 0), (7, 5, 0, 0)]
    raises = [((0, 1), (7, 2), (2, 4)), ((7, 1), (0, 2), (5, 4)),
              ((1, 3), (7, 4), (3, 6)), ((6, 3), (0, 4), (4, 6)),
              ((0, 4), (7, 5), (0, 7)), ((7, 4), (0, 5), (7, 7))]
    images = sum(image_replies(*sample, colour) for colour in (kd.W, kd.B) for sample in samples)
    replies = sum(rank_raise(*sample, colour) for colour in (kd.W, kd.B) for sample in raises)
    rescue = [rank_raise_rescue((0, 1), (4, 2), (2, 4), colour)
              for colour in (kd.W, kd.B)]
    return {'rescue_inputs': 2, 'rescue_first_replies': sum(x[0] for x in rescue),
            'hanging_reply_branches': sum(x[1] for x in rescue),
            'rescue_second_replies': sum(x[2] for x in rescue),
            'supplementary_only': True, 'phase_inputs': 24, 'image_returns': images,
            'rank_raise_inputs': 12, 'rank_raise_replies': replies, **controls()}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
