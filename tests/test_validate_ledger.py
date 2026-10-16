import csv
import tempfile
import unittest
from pathlib import Path

from scripts.validate_ledger import COLUMNS, validate


class FrozenLedgerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "LEDGER.csv"

    def write(self, rows):
        with self.path.open("w", newline="", encoding="utf-8") as stream:
            writer = csv.DictWriter(stream, fieldnames=COLUMNS)
            writer.writeheader()
            writer.writerows(rows)

    def sample(self):
        return dict(
            theorem_id="EC-T0001", title="Example", statement_path="statements/a.md",
            local_proof_path="proofs/a.md", lean_file="formal/A.lean",
            lean_declaration="Endgame.a", lean_toolchain="leanprover/lean4:vX",
            proof_commit_sha="a" * 40, verified_utc="2026-10-16T12:00:00Z",
            rule_edition="FIDE 2023", manifest_path="theorems/frozen/EC-T0001/v1.md",
            status="FROZEN", notes="synthetic fixture, not a real theorem",
        )

    def test_empty_ledger_is_valid(self):
        self.write([])
        self.assertEqual(validate(self.path), 0)

    def test_complete_synthetic_entry_is_structurally_valid(self):
        self.write([self.sample()])
        self.assertEqual(validate(self.path), 1)

    def test_duplicate_ids_rejected(self):
        row = self.sample()
        self.write([row, row])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            validate(self.path)

    def test_unverified_entries_rejected(self):
        row = self.sample()
        row["status"] = "PROPOSED"
        self.write([row])
        with self.assertRaisesRegex(ValueError, "only FROZEN"):
            validate(self.path)

    def test_unpinned_commit_rejected(self):
        row = self.sample()
        row["proof_commit_sha"] = "latest"
        self.write([row])
        with self.assertRaisesRegex(ValueError, "full hex SHA"):
            validate(self.path)

    def test_missing_evidence_rejected(self):
        row = self.sample()
        row["lean_declaration"] = ""
        self.write([row])
        with self.assertRaisesRegex(ValueError, "missing fields"):
            validate(self.path)


if __name__ == "__main__":
    unittest.main()
