#!/usr/bin/env python3
"""Serial verification of finite-native-existence localization; no barrier-existence claim."""
import hashlib, json, os, re, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path("verification/ode-two-barrier-smooth")
OUT.mkdir(parents=True, exist_ok=True)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
BASE = "70cb5f533db3755922378f2324a928398ac4b3a2"
MODULES = ["ODETwoBarrierLocalization", "ODETwoBarrierLocalizationPatch",
           "ODETwoBarrierSmoothAssembly", "ODETwoBarrierSmooth"]
def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
baseline = json.loads((OUT / "baseline.json").read_text())
for p, h in baseline.items():
    assert digest(p) == h, ("Changed baseline input", p)
assert digest("docs/reference/exact_liouville_comparison.tex") == "8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576"
decls = []
for mod in MODULES:
    p = Path("ExactLiouvilleComparison") / (mod + ".lean")
    source = p.read_text()
    assert not re.search(r"\b(sorry|sorryAx|admit|axiom)\b", source), p
    namespaces = []
    for line in source.splitlines():
        if m := re.match(r"namespace (\S+)", line):
            namespaces.append(m[1])
        elif re.match(r"end(?: |$)", line):
            if namespaces: namespaces.pop()
        elif m := re.match(r"(def|structure|theorem) ([^\s({]+)", line):
            decls.append({"file": str(p), "kind": m[1], "name": ".".join(namespaces + [m[2]])})
names = [d["name"] for d in decls]
assert len(names) == len(set(names))
(OUT / "declarations.json").write_text(json.dumps(decls, indent=2) + "\n")
for label, command in [("Types", "#check"), ("AxiomAudit", "#print axioms")]:
    (OUT / (label + ".lean")).write_text(
        "import ExactLiouvilleComparison.ODETwoBarrierSmooth\n" +
        "\n".join(command + " " + n for n in names) +
        '\n#eval IO.println "TWO_BARRIER_SMOOTH_' + label.upper() + '_COMPLETE"\n')
manifest = json.loads(Path("lake-manifest.json").read_text())
pins = {p["name"]: p["rev"] for p in manifest["packages"]}
assert pins["mathlib"] == "d13f23b723b8a846827a245b89c10fc7d3f11612"
assert pins["fsfltz"] == "1a3d387cfacc746e25aad31e5b27b1803103e7cb"
for pkg in ["mathlib", "fsfltz"]:
    directory = ".lake/packages/" + pkg
    assert subprocess.check_output(["git", "-C", directory, "rev-parse", "HEAD"], text=True).strip() == pins[pkg]
    assert not subprocess.check_output(["git", "-C", directory, "status", "--porcelain"], text=True).strip()
assert Path("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
sources = sorted(set(list(baseline) + ["ExactLiouvilleComparison/" + n + ".lean" for n in MODULES] +
    ["docs/ode-two-barrier-smooth.md", "scripts/verify-ode-two-barrier-smooth.py"] +
    [str(p) for p in OUT.iterdir() if p.suffix in {".lean", ".md"}] +
    [str(OUT / "baseline.json"), str(OUT / "declarations.json")]))
before = {p: digest(p) for p in sources}
checks = []
logs = {}
managed = bool(os.environ.get("HORIZON_LEAN_BUILD"))
# Buffer output outside the source checkout until all checks finish. This keeps
# managed fingerprints identical without changing repository ignore rules.
for label, args, marker in [
    ("build", ["ExactLiouvilleComparison.ODETwoBarrierSmooth"], None),
    ("types", ["--lean", str(OUT / "Types.lean")], "TWO_BARRIER_SMOOTH_TYPES_COMPLETE"),
    ("axioms", ["--lean", str(OUT / "AxiomAudit.lean")], "TWO_BARRIER_SMOOTH_AXIOMAUDIT_COMPLETE")]:
    cmd = (["horizon-lean-check"] + args if managed else
           ["lake", "env", "lean", args[1]] if args[0] == "--lean" else ["lake", "build"] + args)
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    logs[label] = result.stdout
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    record = {"command": cmd, "returncode": result.returncode}
    if managed:
        record["managed"] = json.loads([s for s in result.stdout.splitlines() if s.startswith("{")][-1])
        assert record["managed"]["ok"] and record["managed"]["snapshot_verified"]
    if marker:
        assert marker in result.stdout.splitlines(), ("Missing output", label)
    if label == "types":
        for n in names:
            assert re.search(r"^" + re.escape(n) + r"(?:\s|[.{:])", result.stdout, re.M), n
    if label == "axioms":
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
        reports += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)]
        assert sorted(n for n, _ in reports) == sorted(names)
        record["declarations"] = {}
        for n, a in reports:
            axioms = set(filter(None, re.split(r"[,\s]+", a)))
            assert axioms <= ALLOWED, (n, axioms)
            record["declarations"][n] = sorted(axioms)
    checks.append(record)
assert before == {p: digest(p) for p in sources}, "Source changed during verification"
if managed:
    assert len({c["managed"]["source_key"] for c in checks}) == 1
for label, output in logs.items():
    (OUT / (label + ".log")).write_text(output)
(OUT / "receipt.json").write_text(json.dumps({
    "scope": "Generic finite-native-existence to full unchanged Evolution bridge; finite existence remains the parent obligation.",
    "baseline_commit": BASE, "source_sha256": before, "pins": pins, "checks": checks,
    "declaration_count": len(names), "allowed_axioms": sorted(ALLOWED)}, indent=2) + "\n")
print("Verified", len(names), "declarations; full finite-existence localization bridge; allowed-only transitive axioms.")
