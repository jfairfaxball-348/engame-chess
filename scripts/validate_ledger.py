#!/usr/bin/env python3
"""Structural validation only: NOT a mathematical or Lean proof check."""
import argparse
import csv
import re
from pathlib import Path

COLUMNS = [
    "theorem_id", "title", "statement_path", "local_proof_path",
    "lean_file", "lean_declaration", "lean_toolchain",
    "proof_commit_sha", "verified_utc", "rule_edition",
    "manifest_path", "status", "notes",
]
REQUIRED = [x for x in COLUMNS if x != "notes"]


def validate(path: Path) -> int:
    """Raise ValueError on malformed records, return frozen theorem count."""
    with path.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        if reader.fieldnames != COLUMNS:
            raise ValueError("ledger header differs from the frozen schema")
        seen = set()
        for index, row in enumerate(reader, start=2):
            if None in row or any(value is None for value in row.values()):
                raise ValueError(f"line {index}: invalid CSV column count")
            ident = row["theorem_id"]
            if not re.fullmatch(r"EC-T[0-9]{4}", ident):
                raise ValueError(f"line {index}: invalid theorem ID: {ident!r}")
            if ident in seen:
                raise ValueError(f"line {index}: duplicate theorem ID {ident}")
            seen.add(ident)
            if row["status"] != "FROZEN":
                raise ValueError(f"line {index}: only FROZEN theorems belong in the ledger")
            missing = [k for k in REQUIRED if not row[k].strip()]
            if missing:
                raise ValueError(f"line {index}: missing fields: {', '.join(missing)}")
            if not re.fullmatch(r"[0-9a-f]{40}", row["proof_commit_sha"]):
                raise ValueError(f"line {index}: proof commit must be a full hex SHA")
        return len(seen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ledger", type=Path, default=Path(__file__).resolve().parents[1]
        / "theorems" / "LEDGER.csv"
    )
    args = parser.parse_args()
    try:
        count = validate(args.ledger)
    except (ValueError, OSError) as exc:
        parser.exit(1, f"LEDGER INVALID: {exc}\n")
    print(f"LEDGER VALID: {count} frozen theorem(s) (structure only)")


if __name__ == "__main__":
    main()
