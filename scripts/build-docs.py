"""Build both mathematical PDFs from their editable LaTeX sources."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
engine = shutil.which("tectonic")
if engine is None:
    raise SystemExit("Install Tectonic and make it available on PATH.")
for name in ("target-theorem", "proof-blueprint"):
    subprocess.run(
        [engine, "--keep-logs", "--outdir", str(root), name + ".tex"],
        cwd=root / "docs" / "tex", check=True,
    )
    print(root / (name + ".pdf"), flush=True)
