"""Regression tests for the EC-C003 diagnostic. Supplementary evidence only."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import knk_diagnostic as knk  # noqa: E402

W, B = knk.W, knk.B


def pos(wk, wn, bk):
    return {(W, "K"): wk, (W, "N"): wn, (B, "K"): bk}


class KNKDiagnosticTest(unittest.TestCase):
    def test_knight_offsets_are_art_3_6(self):
        g = knk.check_geometry()
        self.assertEqual(g["knight_targets_not_8_offsets"], 0)
        self.assertEqual(g["knight_move_same_colour"], 0)

    def test_corner_check_has_orthogonal_escapes(self):
        # Black Ka8 checked by Nb6; White Kc6 covers b7 only.
        p = pos((2, 5), (1, 5), (0, 7))
        self.assertTrue(knk.in_check(p, B))
        dests = {s[(B, "K")] for s in knk.legal_moves(p, B)}
        self.assertEqual(dests, {(0, 6), (1, 7)})

    def test_checking_knight_can_cover_a_diagonal_neighbour(self):
        # Black Kb2 checked by Nc4, which also covers a3 (a DIAGONAL neighbour of b2).
        # Refutes the S011 prompt's claim that diagonal neighbours are never covered.
        p = pos((7, 7), (2, 3), (1, 1))
        self.assertTrue(knk.in_check(p, B))
        dests = {s[(B, "K")] for s in knk.legal_moves(p, B)}
        self.assertNotIn((0, 2), dests)
        self.assertEqual(len(dests), 7)

    def test_unprotected_knight_capture_gives_kk(self):
        # Black Kb2 takes the unprotected Nc3 (White Kh8 far away).
        p = pos((7, 7), (2, 2), (1, 1))
        caps = [s for s in knk.legal_moves(p, B) if (W, "N") not in s]
        self.assertEqual(len(caps), 1)

    def test_known_stalemate(self):
        # Black Ka8, White Kb6, White Nc6, Black to move: stalemate, no check.
        p = pos((1, 5), (2, 5), (0, 7))
        self.assertFalse(knk.in_check(p, B))
        self.assertEqual(knk.legal_moves(p, B), [])

    def test_mutant_mate_detected(self):
        # Knight with an extra king step on b7, protected by Kb6: Ka8 is mated.
        p = pos((1, 5), (1, 6), (0, 7))
        self.assertTrue(knk.in_check(p, B, mutant=True))
        self.assertEqual(knk.legal_moves(p, B, mutant=True), [])

    def test_geometry_claims(self):
        g = knk.check_geometry()
        for key, v in g.items():
            with self.subTest(key=key):
                if key in knk.GEOMETRY_POSITIVE:
                    self.assertGreater(v, 0)
                else:
                    self.assertEqual(v, 0)

    def test_exhaustive_one_orientation(self):
        r = knk.run(orientations=(W,))
        for key in knk.EXPECTED_ZERO:
            with self.subTest(key=key):
                self.assertEqual(r[key], 0)
        self.assertEqual(r["placements"], 64 * 63 * 62 * 2)


if __name__ == "__main__":
    unittest.main()
