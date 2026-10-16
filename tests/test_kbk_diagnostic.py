"""Regression tests for the EC-C002 diagnostic. Supplementary evidence only."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import kbk_diagnostic as kbk  # noqa: E402

W, B = kbk.W, kbk.B


def pos(wk, wb, bk):
    return {(W, "K"): wk, (W, "B"): wb, (B, "K"): bk}


class KBKDiagnosticTest(unittest.TestCase):
    def test_bishop_ray_blocked_by_king(self):
        # White Bc3, White Kd4: the a1-h8 diagonal is blocked beyond d4.
        p = pos((3, 3), (2, 2), (7, 7))
        self.assertFalse(kbk.in_check(p, B))

    def test_corner_check_has_orthogonal_escape(self):
        # Black Ka8 checked by Bd5; White Kb6 covers a7 and b7 but not b8.
        p = pos((1, 5), (3, 4), (0, 7))
        self.assertTrue(kbk.in_check(p, B))
        dests = {s[(B, "K")] for s in kbk.legal_moves(p, B)}
        self.assertEqual(dests, {(1, 7)})

    def test_unprotected_bishop_capture_gives_kk(self):
        # Black Kb2 captures unprotected Bc3 (White Kh8 far away).
        p = pos((7, 7), (2, 2), (1, 1))
        caps = [s for s in kbk.legal_moves(p, B) if (W, "B") not in s]
        self.assertEqual(len(caps), 1)

    def test_known_stalemate(self):
        # Black Ka8, White Kb6, White Bc7, Black to move: stalemate, no check.
        p = pos((1, 5), (2, 6), (0, 7))
        self.assertFalse(kbk.in_check(p, B))
        self.assertEqual(kbk.legal_moves(p, B), [])

    def test_exhaustive_one_orientation(self):
        r = kbk.run(orientations=(W,))
        for key in kbk.EXPECTED_ZERO:
            with self.subTest(key=key):
                self.assertEqual(r[key], 0)
        self.assertEqual(r["placements"], 64 * 63 * 62 * 2)


if __name__ == "__main__":
    unittest.main()
