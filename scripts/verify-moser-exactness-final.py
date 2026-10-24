#!/usr/bin/env python3
"""Exact-source managed verification of both full bounded Moser exactness targets."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path("verification/moser-exactness")
TEMP = Path(tempfile.mkdtemp(prefix="moser-final-", dir=os.environ["TMPDIR"]))
ENV = dict(os.environ, MOSER_FINAL_AUDIT_DIR=str(TEMP))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
BASE = "f8b5b6bcb56a18c0094d15fed4619ff100327e30"
PINS = {"mathlib": "d13f23b723b8a846827a245b89c10fc7d3f11612",
        "fsfltz": "1a3d387cfacc746e25aad31e5b27b1803103e7cb"}

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

manifest = json.loads(Path("lake-manifest.json").read_text())
assert {p["name"]: p["rev"] for p in manifest["packages"]}.items() >= PINS.items()
assert Path("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
for pkg, rev in PINS.items():
    assert subprocess.check_output(["git", "-C", ".lake/packages/"+pkg,
        "rev-parse", "HEAD"], text=True).strip() == rev
    subprocess.run(["git", "-C", ".lake/packages/"+pkg, "diff", "--exit-code"], check=True,
        stdout=subprocess.DEVNULL)
base_files = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE], text=True).splitlines()
base_files = [p for p in base_files if p.endswith(".lean") or p in
    ["lake-manifest.json", "lakefile.toml", "lean-toolchain", "docs/objective.md",
     "docs/reference/exact_liouville_comparison.tex", "docs/sdu-continuation.md"]]
for p in base_files:
    expected = subprocess.check_output(["git", "show", BASE+":"+p])
    assert Path(p).read_bytes() == expected, ("Changed accepted source", p)
modules = sorted(list(Path("ExactLiouvilleComparison").glob("MoserExactness*.lean")) +
                 list(Path("ExactLiouvilleComparison").glob("FirstPathExactness*.lean")))
for p in modules:
    assert not re.search(r"\b(sorry|admit|sorryAx|axiom|unsafe)\b", p.read_text()), p
files = sorted(set(base_files + [str(p) for p in modules] +
    ["scripts/verify-moser-exactness-final.py", "docs/moser-exactness-proof.md",
     "docs/moser-exactness-crosswalk.md", str(OUT / "FinalAudit.lean"),
     str(OUT / "FinalConsumer.lean")]))
before = {p: digest(p) for p in files}
checks = []
for label, args, marker in [
    ("build", ["ExactLiouvilleComparison.FirstPathExactness"], None),
    ("audit", ["--lean", str(OUT / "FinalAudit.lean")], "MOSER_FINAL_AUDIT_COMPLETE"),
    ("consumer", ["--lean", str(OUT / "FinalConsumer.lean")], "MOSER_FINAL_CONSUMER_COMPLETE")]:
    cmd = ["horizon-lean-check"] + args
    log = TEMP / (label + ".log")
    with log.open("w") as out:
        proc = subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT, env=ENV, text=True)
    s = log.read_text()
    if proc.returncode:
        print(s)
        raise SystemExit(proc.returncode)
    record = json.loads([line for line in s.splitlines() if line.startswith("{")][-1])
    assert record["ok"] and record["snapshot_verified"], record
    if marker:
        assert marker in s.splitlines(), (label, "Missing completion marker")
    checks.append({"command": cmd, "managed": record})
    print(label + ": passed", flush=True)
names = (TEMP / "names.txt").read_text().splitlines()
assert names and len(names) == len(set(names))
required = ["ExactLiouvilleComparison.MoserExactness.cartanTarget",
    "ExactLiouvilleComparison.MoserExactness.moserExactness",
    "ExactLiouvilleComparison.FirstPathExactness.firstPathExactness",
    "ExactLiouvilleComparison.FirstPathExactness.exactComparison",
    "ExactLiouvilleComparison.MoserExactnessIntegral.target",
    "ExactLiouvilleComparison.MoserExactnessIntegralEuclidean.target"]
assert set(required) <= set(names)
s = (TEMP / "audit.log").read_text()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", s)
reports += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", s)]
assert sorted(n for n, _ in reports) == sorted(names), "Incomplete/duplicate transitive audit"
axioms = {}
for n, used in reports:
    used = re.sub(r"\.\{[^}]*\}", "", used)
    used = set(filter(None, re.split(r"[,\s]+", used)))
    assert used <= ALLOWED, (n, used)
    axioms[n] = sorted(used)
for n in names:
    assert (TEMP / "types" / (n + ".txt")).read_text().startswith(n + " :"), n
assert before == {p: digest(p) for p in files}, "Source drift during exact checks"
assert len({c["managed"]["source_key"] for c in checks}) == 1, "Managed source snapshots differ"
final = OUT / "final"
final.mkdir(exist_ok=True)
for p in TEMP.iterdir():
    if p.is_dir(): shutil.copytree(p, final / p.name, dirs_exist_ok=True)
    else: shutil.copyfile(p, final / p.name)
(final / "axioms.json").write_text(json.dumps(axioms, indent=2)+"\n")
(final / "receipt.json").write_text(json.dumps({
    "scope": "Both unchanged full targets, literal smooth gauge, native derivative/exterior identities and unconditional first-path ExactComparison consumer",
    "mission_id": "1f6c4a8d-7d2b-4696-9a6f-2d9ac61c120b",
    "baseline": BASE, "pins": PINS, "source_sha256": before, "checks": checks,
    "declarations": names, "declaration_count": len(names), "required_exports": required,
    "allowed_axioms": sorted(ALLOWED),
    "type_sha256": {n: digest(final / "types" / (n+".txt")) for n in names},
    "scope_exclusions": ["other three path applications", "full comparison and corollaries", "final PDFs and GitHub upload"]}, indent=2)+"\n")
print(f"Verified full Moser and first-path exactness; {len(names)} declarations, allowed-only axioms.")
