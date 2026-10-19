"""Selected local regression controls only; no class-wide outcome search."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import krk_reentry_diagnostic as reentry


class ReentryDiagnosticTest(unittest.TestCase):
    def test_phase_images_and_safe_rank_raises(self):
        result = reentry.run()
        self.assertGreater(result['image_returns'], 0)
        self.assertGreater(result['rank_raise_replies'], 0)

    def test_hanging_rook_is_repaired_before_another_weak_turn(self):
        for colour in ('W', 'B'):
            first, hanging, second = reentry.rank_raise_rescue(
                (0, 1), (4, 2), (2, 4), colour)
            self.assertGreater(first, 0)
            self.assertGreater(hanging, 0)
            self.assertGreater(second, 0)

    def test_failed_policy_controls(self):
        self.assertTrue(all(reentry.controls().values()))


if __name__ == '__main__':
    unittest.main()
