"""Fast regression test for the independent perft counter (S007). Cross-check only."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import perft  # noqa: E402


class PerftTest(unittest.TestCase):
    def test_depth_1_and_2(self):
        self.assertEqual(perft.perft(perft.start(), 1), 20)
        self.assertEqual(perft.perft(perft.start(), 2), 400)


if __name__ == "__main__":
    unittest.main()
