"""Regression tests for the EC-C001 diagnostic. Supplementary evidence only."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import kk_diagnostic as kk  # noqa: E402


class KKDiagnosticTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = kk.run()

    def test_expected_counts(self):
        for key, value in kk.EXPECTED.items():
            with self.subTest(key=key):
                self.assertEqual(self.report[key], value)

    def test_no_stalemate_and_every_state_has_a_move(self):
        self.assertEqual(self.report["stalemates"], 0)
        self.assertEqual(self.report["admissible_states_without_legal_move"], 0)

    def test_corner_cases(self):
        a1, c1, b2 = (0, 0), (2, 0), (1, 1)
        self.assertEqual(len(kk.king_targets(a1)), 3)
        self.assertFalse(kk.attacks(a1, c1))
        self.assertTrue(kk.attacks(a1, b2))
        # White Ka1, Black Kc1, White to move: only a2 is legal (b1, b2 attacked).
        moves = kk.legal_moves((a1, c1, kk.WHITE))
        self.assertEqual(moves, [((0, 1), c1, kk.BLACK)])


if __name__ == "__main__":
    unittest.main()
