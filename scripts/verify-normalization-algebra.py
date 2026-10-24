#!/usr/bin/env python3
"""Reproduce the bounded matrix normalization proof, consumers, types and axiom audit."""
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
OUT = Path('verification/normalization-algebra')
NS = 'ExactLiouvilleComparison.NormalizationAlgebra'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

pins = {p['name']: p['rev'] for p in json.loads(Path('lake-manifest.json').read_text())['packages']}
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
for name in ('mathlib', 'fsfltz'):
    actual = subprocess.check_output(['git', '-C', f'.lake/packages/{name}', 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == pins[name], (name, actual)
assert digest('docs/reference/exact_liouville_comparison.tex') == '8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576'
assert digest('ExactLiouvilleComparison/CylindricalCompatibilityNormalizationAlgebraStatement.lean') == '9089c2951c21eaa757f5a739bb1f6d976512c659855706638832896f64b26ecc'
modules = sorted(Path('ExactLiouvilleComparison').glob('CylindricalCompatibilityNormalizationAlgebra*.lean'))
source_decls = []
for path in modules:
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b', source), path
    source_decls += [NS + '.' + n for n in re.findall(r'^(?:@\[simp\] )?(?:def|abbrev|lemma|theorem) ([^\s({]+)', source, re.M)]
inputs = sorted(set(modules + list(OUT.glob('*.lean')) +
    list(Path('docs').glob('normalization-algebra*.md')) + [Path(p) for p in (
    'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'docs/objective.md',
    'docs/reference/exact_liouville_comparison.tex', 'scripts/verify-normalization-algebra.py')] +
    [OUT / 'statement-review.md']))
before = {str(p): digest(p) for p in inputs}
checks = []
with tempfile.TemporaryDirectory(prefix='normalization-algebra-', dir=os.environ.get('TMPDIR', '/tmp')) as tmp:
    scratch = Path(tmp)
    logs = {}
    for label, args, output, marker in [
        ('build', ['ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraChecks'], None, None),
        ('inventory', ['--lean', str(OUT / 'Inventory.lean')], 'types.txt', 'NORMALIZATION_ALGEBRA_INVENTORY_COMPLETE'),
        ('axioms', ['--lean', str(OUT / 'Axioms.lean')], 'axioms.tsv', 'NORMALIZATION_ALGEBRA_AXIOMS_COMPLETE'),
    ]:
        env = dict(os.environ)
        if output:
            env['NORMALIZATION_ALGEBRA_AUDIT_OUTPUT'] = str(scratch / output)
        cmd = ['horizon-lean-check', *args]
        proc = subprocess.run(cmd, text=True, capture_output=True, env=env)
        logs[label] = proc.stdout + proc.stderr
        if proc.returncode:
            print(logs[label])
            raise SystemExit(proc.returncode)
        receipt = json.loads(proc.stdout.splitlines()[-1])
        assert receipt['ok'] and receipt['snapshot_verified'], receipt
        if marker:
            assert marker in logs[label], (label, logs[label])
        checks.append(receipt)
    assert before == {str(p): digest(p) for p in inputs}, 'Source changed during checks'
    assert len({c['source_key'] for c in checks}) == 1, 'Source snapshots differ'
    for p in ('types.txt', 'types.txt.names', 'axioms.tsv'):
        shutil.copyfile(scratch / p, OUT / p)
    for label, log in logs.items():
        (OUT / (label + '.log')).write_text(log)
names = (OUT / 'types.txt.names').read_text().splitlines()
assert set(source_decls) <= set(names), set(source_decls) - set(names)
assert '⋯' not in (OUT / 'types.txt').read_text(), 'Elided declaration types'
axioms = {}
for line in (OUT / 'axioms.tsv').read_text().splitlines():
    name, values = line.split('\t')
    used = set(filter(None, values.split(',')))
    assert used <= ALLOWED, (name, used)
    axioms[name] = sorted(used)
assert set(names) == set(axioms)
(OUT / 'receipt.json').write_text(json.dumps({
    'scope': 'Finite real metric symplectic normalization algebra, recovery, arbitrary GL naturality, native coordinate consumers; no smoothness or bundle assembly.',
    'mission': '30bfbe32-1f63-42e8-8279-88f994bffb09',
    'source_sha256': before, 'pins': pins, 'checks': checks,
    'source_declarations': source_decls, 'environment_declaration_count': len(names),
    'axioms': axioms, 'allowed_axioms': sorted(ALLOWED),
    'generated_sha256': {str(OUT / p): digest(OUT / p) for p in ('types.txt', 'types.txt.names', 'axioms.tsv')},
}, indent=2) + '\n')
print(f'Verified normalization algebra: {len(names)} elaborated declarations, allowed-only transitive axioms.')
