#!/usr/bin/env python3
"""Managed exact-source checks for the bounded cylindrical radial metric theorem."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / "verification/finite-type-radial-metric"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PINS = {"mathlib": "d13f23b723b8a846827a245b89c10fc7d3f11612",
        "fsfltz": "1a3d387cfacc746e25aad31e5b27b1803103e7cb"}
assert os.environ.get("HORIZON_LEAN_BUILD"), "Managed Lean policy is required"
manifest = json.loads(Path("lake-manifest.json").read_text())
actual_pins = {p["name"]: p["rev"] for p in manifest["packages"]}
for name, pin in PINS.items():
    assert actual_pins[name] == pin
    assert subprocess.check_output(["git", "-C", f".lake/packages/{name}", "rev-parse", "HEAD"], text=True).strip() == pin
assert Path("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
owned = sorted(Path("ExactLiouvilleComparison").glob("FiniteTypeRadialMetric*.lean"))
source_files = owned + sorted(OUT.glob("*.lean")) + sorted(Path("docs").glob("finite-type-radial-metric*.md")) + [
    Path("scripts/verify-finite-type-radial-metric.py"), Path("ExactLiouvilleComparison/Geometry.lean"),
    Path("ExactLiouvilleComparison/Statement.lean"), Path("ExactLiouvilleComparison/LinearAlgebra.lean"), Path("lake-manifest.json"),
    Path("lakefile.toml"), Path("lean-toolchain"), Path("docs/objective.md"),
    Path("docs/reference/exact_liouville_comparison.tex"), OUT / "statement-review.md"]
def hashes():
    return {str(p.relative_to(ROOT) if p.is_absolute() else p): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in source_files}
before = hashes()
accepted = {'ExactLiouvilleComparison/Geometry.lean': '2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326', 'ExactLiouvilleComparison/Statement.lean': 'ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7', 'ExactLiouvilleComparison/LinearAlgebra.lean': '7c4c02c25b53b4df0bd54b5ff1ba884ff7e2469d6e8040f7fce38c9ecbc993c1', 'ExactLiouvilleComparison/FiniteTypeRadialMetricStatement.lean': '19e07aded10817181abdf3b74effff7c29a2f3dd1dda6e2c45e8dbfb1356cbad', 'docs/finite-type-radial-metric-crosswalk.md': 'b5ac34f09ac0f4113de20a10838d4eca69ee11554b32180e785c11fb94c47d72', 'docs/reference/exact_liouville_comparison.tex': '8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576'}
for path, digest in accepted.items():
    assert before[path] == digest, ("Reviewed semantics changed", path)
dependency_paths = ['mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean', 'mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean', 'mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean', 'mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean', 'mathlib/Mathlib/Geometry/Manifold/LocalDiffeomorph.lean', 'mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean', 'fsfltz/FsFltz/Geometry/Smooth.lean', 'fsfltz/FsFltz/Geometry/Liouville.lean', 'fsfltz/FsFltz/Geometry/BoundarySmooth.lean', 'fsfltz/FsFltz/Geometry/FlowBridge.lean', 'fsfltz/FsFltz/Geometry/ExteriorDerivative.lean']
dependency_hashes = {p: hashlib.sha256((Path(".lake/packages") / p).read_bytes()).hexdigest()
                     for p in dependency_paths}
source_names = []
for p in owned:
    s = p.read_text()
    assert not re.search(r"\b(sorry|sorryAx|admit|axiom)\b", s), p
    ns = re.search(r"^namespace (\S+)", s, re.M).group(1)
    source_names += [ns + "." + n for n in re.findall(r"^(?:def|theorem) ([^\s({]+)", s, re.M)]
receipts = []
outputs = {}
with tempfile.TemporaryDirectory(prefix="finite-type-radial-metric-check-", dir=os.environ.get("TMPDIR")) as td:
    for label, args, marker in [
        ("build", ["ExactLiouvilleComparison.FiniteTypeRadialMetricChecks"], None),
        ("inventory", ["--lean", "verification/finite-type-radial-metric/Inventory.lean"], "FINITE_TYPE_RADIAL_METRIC_INVENTORY_COMPLETE"),
        ("axioms", ["--lean", "verification/finite-type-radial-metric/Axioms.lean"], "FINITE_TYPE_RADIAL_METRIC_AXIOMS_COMPLETE"),
    ]:
        target = Path(td) / label
        env = dict(os.environ, FINITE_TYPE_RADIAL_METRIC_AUDIT_OUTPUT=str(target))
        cmd = ["horizon-lean-check", *args]
        r = subprocess.run(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if r.returncode:
            print(r.stdout)
            raise SystemExit(r.returncode)
        record = json.loads([line for line in r.stdout.splitlines() if line.startswith("{")][-1])
        assert record["ok"] and record["snapshot_verified"], record
        assert hashes() == before, "Source drift"
        if marker:
            assert marker in r.stdout.splitlines(), (label, "missing completion marker")
            outputs[label + ".txt"] = target.read_text()
        if label == "inventory":
            assert "⋯" not in outputs["inventory.txt"], "Elided inventory types"
            names = (Path(str(target) + ".names")).read_text().splitlines()
            assert set(source_names) <= set(names), "Incomplete inventory"
            outputs["inventory.names"] = "\n".join(names) + "\n"
        if label == "axioms":
            audit = {line.split("\t")[0]: sorted(filter(None, line.split("\t")[1].split(",")))
                     for line in outputs["axioms.txt"].splitlines()}
            assert set(audit) == set(names)
            for name, axioms in audit.items():
                assert set(axioms) <= ALLOWED, (name, axioms)
        outputs[label + ".log"] = r.stdout
        receipts.append(record)
    assert len({r["source_key"] for r in receipts}) == 1, "Managed snapshots differ"
assert hashes() == before
inventory_bytes = outputs.pop("inventory.txt").encode()
parts = {}
for i, start in enumerate(range(0, len(inventory_bytes), 600000), 1):
    path = f"inventory-{i:03d}.txt"
    data = inventory_bytes[start:start + 600000]
    (OUT / path).write_bytes(data)
    parts[path] = hashlib.sha256(data).hexdigest()
for path, content in outputs.items():
    (OUT / path).write_text(content)
(OUT / "receipt.json").write_text(json.dumps({
    "scope": "Complete bounded cylindrical end calculation: native derivative, original flow tangent, literal primitive identity and exact original g-dual norm square, with consumers; excludes radius construction and all comparison targets.",
    "inventory_sha256": hashlib.sha256(inventory_bytes).hexdigest(),
    "inventory_parts_sha256": parts,
    "source_sha256": before, "pins": PINS, "dependency_sha256": dependency_hashes,
    "source_declarations": source_names,
    "environment_declaration_count": len(names), "axioms": audit,
    "allowed_axioms": sorted(ALLOWED), "checks": receipts,
}, indent=2) + "\n")
print(f"Verified bounded cylindrical radial metric scope: {len(source_names)} source declarations, {len(names)} environment declarations.")
