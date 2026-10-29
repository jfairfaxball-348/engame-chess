"""Certify the pinned KRK supporting bundle in a clean clone; no chess oracle."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from datetime import datetime, timezone


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    formal = root / "formal"
    lake = Path(os.environ["USERPROFILE"]) / ".elan/bin/lake.exe"
    scope = json.loads((root / "proofs/KRK_BOUNDED_FRONTIER_SCOPE.json").read_text(encoding="utf-8"))
    source = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True)
    if dirty or (formal / ".lake").exists():
        raise SystemExit("Certification requires a clean checkout with no pre-existing formal/.lake")
    out = formal / ".lake/krk-certification"
    out.mkdir(parents=True)
    report = {"source_commit": source, "started_utc": datetime.now(timezone.utc).isoformat(),
              "initial_git_status": dirty, "initial_lake_absent": True,
              "toolchain": (formal / "lean-toolchain").read_text().strip(),
              "packages": json.loads((formal / "lake-manifest.json").read_text())["packages"],
              "module_count": len(scope["modules"]),
              "public_theorem_count": len(scope["public_theorems"]), "commands": []}
    # Verify every frozen module, and record all Lean dependencies/configuration.
    sources = sorted(formal.rglob("*.lean"))
    forbidden = re.compile(r"\b(?:sorry|admit|unsafe|axiom|trace_state)\b")
    for module in scope["modules"]:
        text = (root / module).read_text(encoding="utf-8")
        if forbidden.search(text):
            raise SystemExit("Disallowed token in certified module: " + module)
    configs = [formal / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    (out / "source-sha256.txt").write_text("".join(
        hashlib.sha256(p.read_bytes()).hexdigest() + "  " + p.relative_to(root).as_posix() + "\n"
        for p in sorted(set(sources + configs))), encoding="utf-8")
    runner = out / "Declarations.lean"
    lines = ["import EndgameChess", "set_option pp.width 120"]
    for module in scope["modules"]:
        lines.append("import " + module.removeprefix("formal/").removesuffix(".lean").replace("/", "."))
    # Imports must precede commands.
    lines.remove("set_option pp.width 120")
    lines.append("set_option pp.width 120")
    for entry in scope["public_theorems"]:
        name = entry["declaration"]
        lines.extend(["#check @" + name, "#print axioms " + name])
    runner.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def run(args: list[str], log: str) -> None:
        start = time.monotonic()
        with (out / log).open("wb") as stream:
            result = subprocess.run(args, cwd=formal, stdout=stream, stderr=subprocess.STDOUT)
        report["commands"].append({"args": args, "cwd": str(formal), "log": log,
                                   "exit_code": result.returncode,
                                   "seconds": round(time.monotonic() - start, 3)})
        print(log + ": exit " + str(result.returncode), flush=True)
        (out / "summary.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        if result.returncode:
            raise SystemExit(result.returncode)

    run([str(lake), "build"], "build.log")
    run([str(lake), "env", "lean", str(runner)], "axioms-and-types.log")
    run([str(lake), "env", "lean", "AxiomCheck.lean"], "aggregate-axioms.log")
    observed: set[str] = set()
    reports = 0
    for log in ("axioms-and-types.log", "aggregate-axioms.log"):
        text = (out / log).read_text(encoding="utf-8")
        if "sorryAx" in text or re.search(r"(?m)^.*error:", text):
            raise SystemExit("Invalid axiom/type output: " + log)
        for names in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text):
            reports += 1
            observed.update(n.strip() for n in names.split(",") if n.strip())
    if not observed <= {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit("Unexpected axioms: " + repr(observed))
    theorem_output = (out / "axioms-and-types.log").read_text(encoding="utf-8")
    for entry in scope["public_theorems"]:
        if "'" + entry["declaration"] + "' " not in theorem_output:
            raise SystemExit("Missing axiom report: " + entry["declaration"])
    report.update({"observed_axioms": sorted(observed), "axiom_report_count": reports,
                   "completed_utc": datetime.now(timezone.utc).isoformat(), "result": "PASS"})
    (out / "summary.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("source_commit", "module_count", "public_theorem_count", "result")}))


if __name__ == "__main__":
    main()
