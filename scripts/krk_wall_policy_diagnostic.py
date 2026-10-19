#!/usr/bin/env python3
"""S029 selected strategy trajectories, not a game-value search or class proof.
The policy uses coordinates only; legal moves are independently ray-generated.
Defence selectors inspect immediate replies without searching their game values.
"""
import json
import krk_diagnostic as kd
from krk_check_phase_diagnostic import position, move, distance


def far_file(w):
    return 0 if w[0] >= 4 else 7


def wait_file(r, w):
    if w[0] >= 4:
        return 1 if r[0] == 0 else 0
    return 6 if r[0] == 7 else 7


class WallRun:
    def __init__(self, s, r, w, strong, defence):
        self.p = position(s, r, w, strong)
        self.strong, self.weak = strong, kd.OTHER[strong]
        self.defence = defence
        self.plies = 0
        self.events = {'wait': 0, 'normalize': 0, 'chase': 0,
                       'raise': 0, 'catch_up': 0, 'check': 0}
        self.done = False

    def squares(self):
        return self.p[(self.strong, 'K')], self.p[(self.strong, 'R')], self.p[(self.weak, 'K')]

    def choose_defence(self, replies):
        s, r, w = self.squares()
        def key(p):
            v = p[(self.weak, 'K')]
            if self.defence == 'low_away':
                return (v[1], -abs(v[0]-s[0]), v[0])
            if self.defence == 'rook_pressure':
                return (distance(v, r), v[1], v[0])
            if self.defence == 'up':
                return (-v[1], abs(v[0]-s[0]), v[0])
            # Alternate local lateral preferences; no evaluation or lookahead.
            return (v[1], v[0] if (self.plies//2) % 2 else -v[0])
        return min(replies, key=key)

    def action(self, piece, target, event):
        self.p = move(self.p, self.strong, (self.strong, piece), target)
        self.plies += 1
        self.events[event] += 1
        replies = kd.legal_moves(self.p, self.weak)
        if not replies:
            assert kd.in_check(self.p, self.weak), ('stalemate', self.p, event)
            self.done = True
            return
        assert all((self.strong, 'R') in p for p in replies), ('capture', self.p, event)
        self.p = self.choose_defence(replies)
        self.plies += 1

    def run(self):
        while not self.done:
            assert self.plies < 1000, ('policy did not terminate', self.p)
            s, r, w = self.squares()
            assert s[1] < r[1] < w[1], ('wall lost', self.p)
            if abs(r[0]-w[0]) < 2:
                self.action('R', (far_file(w), r[1]), 'normalize')
            elif w[1] >= r[1]+2:
                self.action('R', (r[0], r[1]+1), 'raise')
            elif s[1]+2 <= r[1]:
                self.action('K', (s[0], s[1]+1), 'catch_up')
            elif s[0] == w[0]:
                self.action('R', (r[0], w[1]), 'check')
            elif abs(s[0]-w[0]) == 1:
                self.action('R', (wait_file(r, w), r[1]), 'wait')
            elif abs(r[0]-w[0]) >= 3:
                self.action('K', (s[0]+(1 if w[0]>s[0] else -1), s[1]), 'chase')
            else:
                self.action('R', (far_file(w), r[1]), 'normalize')
        return {'plies': self.plies, **self.events}


def direct_setup_controls():
    p = position((0, 0), (3, 3), (2, 2), kd.W)
    for target in [(3, 1), (1, 3)]:
        q = move(p, kd.W, (kd.W, 'R'), target)
        capture = dict(q)
        del capture[(kd.W, 'R')]
        capture[(kd.B, 'K')] = target
        assert capture in kd.legal_moves(q, kd.B)
    return True


def run():
    samples = [((1, 1), (7, 2), (2, 3)),  # old chase cycle
               ((6, 1), (0, 2), (5, 3)),  # opposite orientation
               ((2, 1), (6, 2), (4, 3)),  # offset-two margin-two normalization
               ((5, 1), (1, 2), (3, 3)),  # d/e switch in opposite direction
               ((0, 0), (1, 2), (2, 3)),  # threatened strong-turn rook
               ((0, 0), (7, 5), (2, 7)),  # large catch-up gap
               ((5, 5), (0, 6), (7, 7)),  # protected-corner stalemate trap avoided
               ((2, 5), (0, 6), (2, 7))]  # two-file edge mate
    results = [WallRun(*sample, colour, defence).run()
               for colour in [kd.W, kd.B]
               for defence in ['low_away', 'rook_pressure', 'up', 'alternate']
               for sample in samples]
    events = {k: sum(x[k] for x in results) for k in results[0] if k != 'plies'}
    assert all(v > 0 for v in events.values())
    return {'supplementary_only': True, 'selected_trajectories': len(results),
            'max_observed_plies': max(x['plies'] for x in results),
            'events': events, 'direct_setup_capture_controls': direct_setup_controls()}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
