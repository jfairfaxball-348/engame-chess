"""Regression tests for the EC-C007/EC-C008 diagnostic. Supplementary evidence only."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import krk_diagnostic as krk  # noqa: E402

W, B = krk.W, krk.B


def pos(wk, wr, bk):
    return {(W, "K"): wk, (W, "R"): wr, (B, "K"): bk}


class KRKDiagnosticTest(unittest.TestCase):
    def test_forced_rook_capture(self):
        # Black Ka1, White Rb2 (unprotected), White Kh8, Black to move: only Kxb2.
        p = pos((7, 7), (1, 1), (0, 0))
        self.assertFalse(krk.in_check(p, B))
        succ = krk.legal_moves(p, B)
        self.assertEqual(len(succ), 1)
        self.assertNotIn((W, "R"), succ[0])

    def test_protected_rook_is_not_capturable(self):
        # Same, but White Kc3 protects b2: no legal move at all (stalemate).
        p = pos((2, 2), (1, 1), (0, 0))
        self.assertFalse(krk.in_check(p, B))
        self.assertEqual(krk.legal_moves(p, B), [])

    def test_rook_ray_blocked_by_king(self):
        # White Ra1, White Kd1, Black Kh1: the first rank is blocked at d1.
        p = pos((3, 0), (0, 0), (7, 0))
        self.assertFalse(krk.in_check(p, B))

    def test_xray_after_king_step(self):
        # Black Kd8 checked by Ra8; e8 lies behind the king on the same rank and is
        # attacked once the king has left d8.
        p = pos((3, 5), (0, 7), (3, 7))
        dests = {s[(B, "K")] for s in krk.legal_moves(p, B)}
        self.assertNotIn((4, 7), dests)

    def test_back_rank_mate(self):
        # Black Kh8, White Kh6, White Ra8: checkmate.
        p = pos((7, 5), (0, 7), (7, 7))
        self.assertTrue(krk.in_check(p, B))
        self.assertEqual(krk.legal_moves(p, B), [])

    def test_exhaustive_one_orientation(self):
        r, examples = krk.run(W)
        for key in krk.EXPECTED_ZERO:
            with self.subTest(key=key):
                self.assertEqual(r[key], 0, examples)
        self.assertEqual(r["dead_states"], r["stalemates"] + r["forced_rook_captures"])


if __name__ == "__main__":
    unittest.main()
