"""Spot tests for the EC-C008 route simulator (supplementary). The exhaustive run is
`python scripts/krk_route.py` (about 7 minutes)."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import krk_route as kr  # noqa: E402


def reaches_mate(S, R, L):
    try:
        kr.route(S, R, L)
    except kr.Mated:
        return True
    return False


class KRKRouteTest(unittest.TestCase):
    def test_escort_from_centre(self):
        self.assertTrue(reaches_mate((3, 4), (0, 0), (6, 1)))

    def test_detour_case(self):
        # Rook on rank 8 behind its own king on rank 8 (needs the P1e detour).
        self.assertTrue(reaches_mate((1, 7), (0, 7), (1, 3)))

    def test_lemma_m_pattern(self):
        # L=(0,0), S=(0,2), rook h8, strong to move: one move mates.
        g = kr.Game((0, 2), (7, 7), (0, 0))
        with self.assertRaises(kr.Mated):
            g.play((kr.W, "R"), (7, 0), "mate")

    def test_sample_of_states(self):
        for k, (S, R, L) in enumerate(kr.strong_to_move_states()):
            if k % 997 == 0:
                with self.subTest(S=S, R=R, L=L):
                    self.assertTrue(reaches_mate(S, R, L))


if __name__ == "__main__":
    unittest.main()
