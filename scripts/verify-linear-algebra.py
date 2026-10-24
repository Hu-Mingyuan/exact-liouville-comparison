#!/usr/bin/env python3
"""Verify the bounded weak-taming lemma; never certify the comparison theorem."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / 'verification/linear-algebra'
DECLARATIONS = json.loads((OUT / 'declarations.json').read_text())
SOURCES = [Path(p) for p in [
    'ExactLiouvilleComparison/Geometry.lean',
    'ExactLiouvilleComparison/Statement.lean',
    'ExactLiouvilleComparison/LinearAlgebra.lean',
    'ExactLiouvilleComparison/LinearAlgebraChecks.lean',
    'verification/linear-algebra/AxiomAudit.lean',
    'verification/linear-algebra/Types.lean',
    'verification/linear-algebra/declarations.json',
    'scripts/verify-linear-algebra.py', 'docs/linear-algebra.md',
    'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
    'docs/reference/exact_liouville_comparison.tex']]
def hashes():
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in SOURCES}
source_hashes = hashes()
accepted = {
    'ExactLiouvilleComparison/Geometry.lean': '2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326',
    'ExactLiouvilleComparison/Statement.lean': 'ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7',
    'docs/reference/exact_liouville_comparison.tex': '8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576',
}
for p, h in accepted.items():
    assert source_hashes[p] == h, ('Accepted source changed', p)
for p in SOURCES:
    if p.suffix == '.lean':
        assert not re.search(r'\b(sorry|admit|axiom|sorryAx)\b', p.read_text()), p
pins = {p['name']: p['rev'] for p in json.loads(Path('lake-manifest.json').read_text())['packages']}
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
for package in ['fsfltz', 'mathlib']:
    actual = subprocess.check_output(['git', '-C', f'.lake/packages/{package}', 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == pins[package], (package, actual)
managed = bool(os.environ.get('HORIZON_LEAN_BUILD'))
targets = ['ExactLiouvilleComparison.LinearAlgebra', 'ExactLiouvilleComparison.LinearAlgebraChecks']
commands = [('build', ['horizon-lean-check', *targets] if managed else ['lake', 'build', *targets])]
for label, file in [('axioms', 'AxiomAudit.lean'), ('types', 'Types.lean')]:
    path = 'verification/linear-algebra/' + file
    commands.append((label, ['horizon-lean-check', '--lean', path] if managed else ['lake', 'env', 'lean', path]))
checks = []
# Do not mutate the fingerprinted checkout while a managed check runs.
with tempfile.TemporaryDirectory(prefix='linear-verification-') as scratch:
    logs = {}
    for label, command in commands:
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        logs[label] = result.stdout
        Path(scratch, label + '.log').write_text(result.stdout)
        receipt = {'command': command, 'returncode': result.returncode}
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
        if managed:
            obj = json.loads([s for s in result.stdout.splitlines() if s.startswith('{')][-1])
            assert obj['ok'] and obj['snapshot_verified'], obj
            receipt['managed'] = obj
        assert len(result.stdout.encode()) < 250000 and 'truncated' not in result.stdout.lower(), label
        if label == 'axioms':
            reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
            reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)]
            assert sorted(n for n, _ in reports) == sorted(DECLARATIONS), reports
            ax = {n: list(filter(None, re.split(r'[,\s]+', a))) for n, a in reports}
            for n, a in ax.items():
                assert set(a) <= {'propext', 'Classical.choice', 'Quot.sound'}, (n, a)
            receipt['transitive_axioms'] = ax
        if label == 'types':
            for name in DECLARATIONS:
                assert name in result.stdout, ('Missing type', name)
            assert '⋯' not in result.stdout, 'Elaborated types elided'
        checks.append(receipt)
    assert hashes() == source_hashes, 'Source changed during verification'
    for label, log in logs.items():
        (OUT / (label + '.log')).write_text(log)
(OUT / 'receipt.json').write_text(json.dumps({
    'scope': 'Proved weak-taming linear algebra and native radial pointwise consumer only; no comparison theorem or flow.',
    'accepted_base_commit': '46fccea69cb9524882bbeda83b0ac2067d22a149',
    'accepted_statement_review_artifact': '8930b2e3-ab88-498e-8a6f-d3f732fa8f95',
    'source_sha256': source_hashes, 'pins': pins, 'checks': checks,
    'declarations': DECLARATIONS,
}, indent=2) + '\n')
print(f'Bounded module and consumer passed; {len(DECLARATIONS)} transitive audits and complete types saved.')
