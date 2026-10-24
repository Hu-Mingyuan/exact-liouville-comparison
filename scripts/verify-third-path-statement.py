#!/usr/bin/env python3
"""Serial managed checks of the third-path statement gate, not its existence proof."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification/third-path"
COMMANDS = [
    ("statement-check", ["horizon-lean-check", "ExactLiouvilleComparison.ThirdPathStatement"]),
    ("statement-inventory-check", ["horizon-lean-check", "--lean",
                                   "verification/third-path/StatementInventory.lean"]),
]


def main():
    # Do not change the fingerprinted tree while either managed check is running.
    with tempfile.TemporaryDirectory(prefix="third-path-statement-", dir=os.environ.get("TMPDIR")) as tmp:
        results = []
        for name, command in COMMANDS:
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            Path(tmp, name + ".json").write_text(result.stdout)
            Path(tmp, name + ".stderr").write_text(result.stderr)
            receipt = json.loads(result.stdout)
            results.append((name, receipt))
            if result.returncode or not receipt.get("ok") or not receipt.get("snapshot_verified"):
                raise RuntimeError(f"{name}: check not verified; diagnostics follow\n{result.stdout}\n{result.stderr}")
        OUT.mkdir(parents=True, exist_ok=True)
        for name, _ in results:
            for suffix in (".json", ".stderr"):
                (OUT / (name + suffix)).write_bytes(Path(tmp, name + suffix).read_bytes())
        (OUT / "statement-inventory.txt").write_bytes(
            Path(tmp, "statement-inventory-check.stderr").read_bytes())
    sources = ["ExactLiouvilleComparison/ThirdPathStatement.lean",
               "docs/third-path-crosswalk.md", "verification/third-path/StatementInventory.lean",
               "docs/reference/exact_liouville_comparison.tex", "lean-toolchain",
               "lakefile.toml", "lake-manifest.json"]
    (OUT / "statement-source-hashes.json").write_text(json.dumps(
        {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources}, indent=2) + "\n")
    print("Third-path statement gate checks passed; no existence theorem is certified.")


if __name__ == "__main__":
    main()
