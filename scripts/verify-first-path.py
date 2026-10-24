#!/usr/bin/env python3
"""Reproduce the first-path proof build, accepted-source check and transitive audit."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / "verification"
new_modules = sorted(Path("ExactLiouvilleComparison").glob("FirstPath*.lean"))
source_files = new_modules + [
    Path("verification/FirstPathConsumer.lean"),
    Path("verification/FirstPathAxiomAudit.lean"), Path("verification/FirstPathTypes.lean"),
    Path("verification/FirstPathCrosswalk.md"),
    Path("verification/first-path-base.json"),
    Path("scripts/verify-first-path.py"),
    Path("ExactLiouvilleComparison/Geometry.lean"),
    Path("ExactLiouvilleComparison/Statement.lean"),
    Path("lakefile.toml"), Path("lake-manifest.json"), Path("lean-toolchain"),
]
def hashes():
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files}
inputs = json.loads(Path("verification/first-path-inputs.json").read_text())
for p, entry in inputs.items():
    assert hashlib.sha256(Path(p).read_bytes()).hexdigest() == entry["sha256"], p
source_files += [Path(p) for p in inputs if Path(p) not in source_files]
source_files += [Path("verification/first-path-inputs.json"), Path("verification/first-path-declarations.json")]
before = hashes()
base = json.loads(Path("verification/first-path-base.json").read_text())
for p, expected in base["unchanged_sha256"].items():
    assert hashlib.sha256(Path(p).read_bytes()).hexdigest() == expected, p
for p in source_files:
    if p.suffix == ".lean" and re.search(r"\b(sorry|admit|axiom)\b", p.read_text()):
        raise SystemExit(f"Forbidden token: {p}")
manifest = json.loads(Path("lake-manifest.json").read_text())
pins = {p["name"]: p["rev"] for p in manifest["packages"]}
assert pins["mathlib"] == "d13f23b723b8a846827a245b89c10fc7d3f11612"
assert pins["fsfltz"] == "1a3d387cfacc746e25aad31e5b27b1803103e7cb"
assert Path("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
for package in ("mathlib", "fsfltz"):
    assert subprocess.check_output(["git", "-C", f".lake/packages/{package}",
        "rev-parse", "HEAD"], text=True).strip() == pins[package]
managed = bool(os.environ.get("HORIZON_LEAN_BUILD"))
commands = [
    ("build", ["ExactLiouvilleComparison.FirstPathChecks"], None),
    ("consumer", ["--lean", "verification/FirstPathConsumer.lean"],
        "FIRST_PATH_CONSUMER_COMPLETE"),
    ("types", ["--lean", "verification/FirstPathTypes.lean"], "FIRST_PATH_TYPES_COMPLETE"),
    ("axioms", ["--lean", "verification/FirstPathAxiomAudit.lean"],
        "FIRST_PATH_AXIOMS_COMPLETE"),
]
receipts = []
for label, args, marker in commands:
    if managed:
        cmd = ["horizon-lean-check", *args]
    elif args[0] == "--lean":
        cmd = ["lake", "env", "lean", args[1]]
    else:
        cmd = ["lake", "build", *args]
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (OUT / f"first-path-{label}.log").write_text(result.stdout)
    entry = {"command": cmd, "returncode": result.returncode}
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    if managed:
        lines = [s for s in result.stdout.splitlines() if s.startswith("{")]
        entry["managed"] = json.loads(lines[-1])
        assert entry["managed"]["ok"] and entry["managed"]["snapshot_verified"], entry
    if marker:
        assert marker in result.stdout.splitlines(), f"Missing {marker}"
        assert "output truncated" not in result.stdout.lower(), label
        assert len(result.stdout.encode()) < 250_000, label
        audit_source = Path(args[-1]).read_text()
        expected_types = re.findall(r"^#check (\S+)$", audit_source, re.M)
        expected_prints = re.findall(r"^#print (\S+)$", audit_source, re.M)
        for name in expected_types:
            assert re.search(r"^" + re.escape(name) + r"(?:\s|[.{:])", result.stdout, re.M), name
        for name in expected_prints:
            assert re.search(r"^(?:def|theorem) " + re.escape(name) + r"(?:\s|[.{:])", result.stdout, re.M), name
        entry["elaborated_types"] = expected_types + expected_prints
        expected = re.findall(r"^#print axioms (\S+)$", audit_source, re.M)
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
        reports += [(n, "") for n in re.findall(
            r"'([^']+)' does not depend on any axioms", result.stdout)]
        assert sorted(n for n, _ in reports) == sorted(expected), (label, expected, reports)
        entry["declarations"] = {}
        for name, ax in reports:
            axioms = set(filter(None, re.split(r"[,\s]+", ax)))
            assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, (name, axioms)
            entry["declarations"][name] = sorted(axioms)
    receipts.append(entry)
assert before == hashes(), "Sources changed during verification"
(OUT / "first-path-receipt.json").write_text(json.dumps({
    "scope": "First-path pointwise construction, estimates and proper exhaustion only. No joint smoothness of X, compact-core uniform derivative bounds, ODE completeness, MainTarget or phase acceptance.",
    "base": base, "source_sha256": before, "pins": pins,
    "checks": receipts,
}, indent=2) + "\n")
print("First-path estimates and exhaustion, generic consumers, types and transitive axiom checks passed.")
