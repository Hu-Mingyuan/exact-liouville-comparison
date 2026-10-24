#!/usr/bin/env python3
"""Check the constructed third-path field and estimates; no evolution acceptance claim."""
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
MODULES = ["ThirdPathStatement", "ThirdPathField", "ThirdPathEstimates", "ThirdPathEndpoints"]


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
    (OUT / "input-declarations.json").write_text(json.dumps(declarations, indent=2) + "\n")
    header = "import ExactLiouvilleComparison.ThirdPathEndpoints\n"
    type_code = header + "set_option pp.universes true\nset_option pp.fullNames true\n"
    type_code += "open Lean Elab Command in\nrun_cmd do\n  let mut lines : Array String := #[]\n"
    type_code += "  for n in [" + ", ".join("``" + n for n in names) + "] do\n"
    type_code += '''    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    let line := s!"{n} : {ty.pretty}"
    lines := lines.push line
  let some out ← liftIO (IO.getEnv "THIRD_PATH_TYPE_OUTPUT") | throwError "Missing type output path"
  liftIO <| IO.FS.writeFile out (String.intercalate "\\n" lines.toList ++ "\\n")
'''
    type_code += '#eval IO.println "THIRD_INPUT_TYPES_COMPLETE"\n'
    (OUT / "InputTypes.lean").write_text(type_code)
    (OUT / "InputAxioms.lean").write_text(header + "\n".join("#print axioms " + n for n in names)
        + '\n#eval IO.println "THIRD_INPUT_AXIOMS_COMPLETE"\n')
    paths = sorted(set(baseline["files"]) | {d["file"] for d in declarations} | {
        "docs/third-path-crosswalk.md", "verification/third-path/statement-review.md",
        "scripts/verify-third-path-inputs.py", "verification/third-path/baseline.json",
        "verification/third-path/InputTypes.lean", "verification/third-path/InputAxioms.lean"})
    before = {p: digest(ROOT / p) for p in paths}
    managed = bool(os.environ.get("HORIZON_LEAN_BUILD"))
    type_output = Path(tempfile.mkdtemp(prefix="third-types-", dir=os.environ.get("TMPDIR"))) / "types.txt"
    check_env = dict(os.environ, THIRD_PATH_TYPE_OUTPUT=str(type_output))
    checks = []
    outputs = {}
    for label, args, marker in [
        ("build", ["ExactLiouvilleComparison.ThirdPathEndpoints"], None),
        ("types", ["--lean", "verification/third-path/InputTypes.lean"], "THIRD_INPUT_TYPES_COMPLETE"),
        ("axioms", ["--lean", "verification/third-path/InputAxioms.lean"], "THIRD_INPUT_AXIOMS_COMPLETE")]:
        command = (["horizon-lean-check"] + args if managed else
                   ["lake", "env", "lean", args[1]] if args[0] == "--lean" else ["lake", "build"] + args)
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, env=check_env)
        log = result.stderr + result.stdout
        # All outputs stay out of the source tree until all three checks finish.
        outputs[label] = log
        if result.returncode:
            raise RuntimeError(log)
        record = {"command": command, "returncode": result.returncode}
        if managed:
            record["managed"] = json.loads(result.stdout)
            assert record["managed"]["ok"] and record["managed"]["snapshot_verified"]
        if marker:
            assert marker in log.splitlines(), label
        if label == "types":
            outputs["elaborated-types"] = type_output.read_text()
            for name in names:
                assert name + " : " in outputs["elaborated-types"], name
        if label == "axioms":
            reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
            reports += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", log)]
            assert sorted(n for n, _ in reports) == sorted(names)
            record["declarations"] = {}
            for name, axioms in reports:
                actual = set(filter(None, re.split(r"[,\s]+", axioms)))
                assert actual <= ALLOWED, (name, actual)
                record["declarations"][name] = sorted(actual)
        checks.append(record)
    assert before == {p: digest(ROOT / p) for p in paths}
    if managed:
        assert len({c["managed"]["source_key"] for c in checks}) == 1
    for label, log in outputs.items():
        (OUT / ("inputs-" + label + ".log")).write_text(log)
    (OUT / "inputs-receipt.json").write_text(json.dumps({
        "scope": "Third-path statement, constructed literal field, regularity, g-norm bounds and endpoint identities",
        "source_sha256": before, "input_commit": baseline["input_commit"], "pins": pins,
        "declaration_count": len(names), "checks": checks, "allowed_axioms": sorted(ALLOWED),
        "remaining": ["sqrt(R) scalar applicability", "full evolution construction",
                      "unconditional endpoint consumers", "final source-bound proof review"]
    }, indent=2) + "\n")
    print(f"Verified {len(names)} third-path input declarations; global evolution mission remains open.")


if __name__ == "__main__":
    main()
