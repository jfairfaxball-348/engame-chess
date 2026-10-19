"""Selected local policy regressions; no class-wide outcome computation."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import krk_wall_policy_diagnostic as policy


class WallPolicyTest(unittest.TestCase):
    def test_selected_policy_trajectories_end_in_actual_mate(self):
        result = policy.run()
        self.assertEqual(result['selected_trajectories'], 64)
        self.assertTrue(all(v > 0 for v in result['events'].values()))

    def test_old_chase_cycle_mates_with_tempo_in_both_colours(self):
        for colour in ['W', 'B']:
            for defence in ['low_away', 'alternate']:
                result = policy.WallRun((1, 1), (7, 2), (2, 3), colour, defence).run()
                self.assertGreater(result['wait'], 0)

    def test_direct_geometric_setup_can_lose_the_rook(self):
        self.assertTrue(policy.direct_setup_controls())


if __name__ == '__main__':
    unittest.main()
