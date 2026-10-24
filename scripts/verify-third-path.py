#!/usr/bin/env python3
"""Serial full third-path build, environment declaration inventory and axiom audit."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification/third-path"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MODULES = ["ThirdPathStatement", "ThirdPathField", "ThirdPathEstimates",
           "ThirdPathEndpoints", "ThirdPathExhaustion", "ThirdPathFlow", "ThirdPathFlowConsumers"]
HEADER = """import ExactLiouvilleComparison.ThirdPathFlowConsumers
set_option pp.universes true
set_option pp.fullNames true
open Lean Elab Command in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if (`ExactLiouvilleComparison.ThirdPath).isPrefixOf n ||
        n.toString.startsWith "_private.ExactLiouvilleComparison.ThirdPath" then
      return ns.push n
    return ns
  let names := names.qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "THIRD_PATH_AUDIT_OUTPUT") | throwError "Missing output path"
  let mut lines : Array String := #[]
"""


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    baseline = json.loads((OUT / "baseline.json").read_text())
    for path, expected in baseline["files"].items():
        assert digest(ROOT / path) == expected, ("Changed preserved source", path)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pins = {p["name"]: p["rev"] for p in manifest["packages"]}
    assert pins["mathlib"] == "d13f23b723b8a846827a245b89c10fc7d3f11612"
    assert pins["fsfltz"] == "1a3d387cfacc746e25aad31e5b27b1803103e7cb"
    declarations = []
    for module in MODULES:
        path = f"ExactLiouvilleComparison/{module}.lean"
        source = (ROOT / path).read_text()
        assert not re.search(r"\b(sorry|sorryAx|admit|axiom|unsafe|opaque)\b", source), path
        namespace = re.search(r"^namespace (\S+)", source, re.M).group(1)
        for kind, name in re.findall(r"^(def|abbrev|theorem|structure) ([^\s({]+)", source, re.M):
            declarations.append({"file": path, "kind": kind, "name": namespace + "." + name})
    names = [d["name"] for d in declarations]
    assert len(names) == len(set(names))
    (OUT / "declarations.json").write_text(json.dumps(declarations, indent=2) + "\n")
    inventory = HEADER + '''  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    lines := lines.push s!"{n} : {ty.pretty}"
  liftIO <| IO.FS.writeFile out (String.intercalate "\\n" lines.toList ++ "\\n")
  liftIO <| IO.FS.writeFile (out ++ ".names")
    (String.intercalate "\\n" (names.toList.map Name.toString) ++ "\\n")
#eval IO.println "THIRD_FINAL_INVENTORY_COMPLETE"
'''
    axioms = HEADER + '''  for n in names do
    let axioms ← Lean.collectAxioms n
    lines := lines.push (n.toString ++ "\\t" ++
      String.intercalate "," (axioms.toList.map Name.toString))
  liftIO <| IO.FS.writeFile out (String.intercalate "\\n" lines.toList ++ "\\n")
#eval IO.println "THIRD_FINAL_AXIOMS_COMPLETE"
'''
    (OUT / "FinalInventory.lean").write_text(inventory)
    (OUT / "FinalAxioms.lean").write_text(axioms)
    paths = sorted(set(baseline["files"]) | {d["file"] for d in declarations} | {
        "docs/third-path-crosswalk.md", "verification/third-path/statement-review.md",
        "scripts/verify-third-path.py", "verification/third-path/baseline.json",
        "verification/third-path/FinalInventory.lean", "verification/third-path/FinalAxioms.lean"})
    before = {p: digest(ROOT / p) for p in paths}
    managed = bool(os.environ.get("HORIZON_LEAN_BUILD"))
    scratch = Path(tempfile.mkdtemp(prefix="third-final-", dir=os.environ.get("TMPDIR")))
    checks, outputs = [], {}
    environment_names = []
    audit = {}
    for label, args, marker in [
        ("build", ["ExactLiouvilleComparison.ThirdPathFlowConsumers"], None),
        ("inventory", ["--lean", "verification/third-path/FinalInventory.lean"], "THIRD_FINAL_INVENTORY_COMPLETE"),
        ("axioms", ["--lean", "verification/third-path/FinalAxioms.lean"], "THIRD_FINAL_AXIOMS_COMPLETE")]:
        command = (["horizon-lean-check"] + args if managed else
                   ["lake", "env", "lean", args[1]] if args[0] == "--lean" else ["lake", "build"] + args)
        output = scratch / (label + ".txt")
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
            env=dict(os.environ, THIRD_PATH_AUDIT_OUTPUT=str(output)))
        log = result.stderr + result.stdout
        (scratch / (label + ".log")).write_text(log)
        outputs[label] = log
        if result.returncode:
            raise RuntimeError(log)
        record = {"command": command, "returncode": result.returncode}
        if managed:
            record["managed"] = json.loads(result.stdout)
            assert record["managed"]["ok"] and record["managed"]["snapshot_verified"]
        if marker:
            assert marker in log.splitlines(), label
        if label == "inventory":
            outputs["elaborated-types"] = output.read_text()
            environment_names = Path(str(output) + ".names").read_text().splitlines()
            assert set(names) <= set(environment_names)
            for name in environment_names:
                assert name + " : " in outputs["elaborated-types"], name
        if label == "axioms":
            for line in output.read_text().splitlines():
                name, ax = line.split("\t")
                actual = set(filter(None, ax.split(",")))
                assert actual <= ALLOWED, (name, actual)
                assert name not in audit
                audit[name] = sorted(actual)
            assert set(audit) == set(environment_names)
            assert "ExactLiouvilleComparison.ThirdPath.thirdPathFlow" in audit
            assert "ExactLiouvilleComparison.ThirdPath.inverseEndpoint_direction" in audit
        checks.append(record)
    assert before == {p: digest(ROOT / p) for p in paths}
    if managed:
        assert len({c["managed"]["source_key"] for c in checks}) == 1
    # Save receipts only after every managed check has finished.
    for label, log in outputs.items():
        (OUT / ("final-" + label + ".txt")).write_text(log)
    (OUT / "environment-declarations.json").write_text(json.dumps(environment_names, indent=2) + "\n")
    (OUT / "axiom-audit.json").write_text(json.dumps(audit, indent=2) + "\n")
    (OUT / "receipt.json").write_text(json.dumps({
        "scope": "Constructed third-path field, scalar control, full evolution, reviewed Target and unconditional consumers",
        "source_sha256": before, "input_commit": baseline["input_commit"], "pins": pins,
        "source_declaration_count": len(names), "environment_declaration_count": len(environment_names),
        "checks": checks, "allowed_axioms": sorted(ALLOWED),
        "excluded_root_owned": ["Cartan exactness", "final comparison assembly", "corollaries", "final packaging and acceptance"]
    }, indent=2) + "\n")
    print(f"Verified {len(names)} source declarations and {len(environment_names)} environment declarations, including actual thirdPathFlow.")


if __name__ == "__main__":
    main()
