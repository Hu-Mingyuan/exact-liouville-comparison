#!/usr/bin/env python3
"""Verify complete native normalization, consumers, types and transitive axioms."""
import base64
import gzip
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
OUT = Path('verification/cylindrical-compatibility-normalization')
NS = 'ExactLiouvilleComparison.CylindricalCompatibility.Normalization'
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
assert digest('ExactLiouvilleComparison/CylindricalCompatibilityNormalizationStatement.lean') == 'a100611cd3ccc7a9076e318f3b4fc8e376f1dd9e1fc304004e4adec270ec2fc3'
assert digest('docs/cylindrical-compatibility-normalization-crosswalk.md') == '3c009a3a5bbd22219fff51ac1b6e3ed5140d057b9e3c48d95c74e0a1f8ab906c'
# Child sources are integrated exactly as independently accepted.
for receipt in ('verification/normalization-algebra/receipt.json', 'verification/normalization-sqrt/receipt.json'):
    bindings = json.loads(Path(receipt).read_text())['source_sha256']
    for path, sha in bindings.items():
        if path.startswith('ExactLiouvilleComparison/CylindricalCompatibilityNormalization'):
            assert digest(path) == sha, ('Child source changed', path)
modules = sorted(Path('ExactLiouvilleComparison').glob('CylindricalCompatibilityNormalization*.lean'))
source_decls = []
for path in modules:
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|sorryAx)\b|^\s*(?:(?:private|protected)\s+)?axiom\s', source, re.M), path
    namespace = ('ExactLiouvilleComparison.NormalizationAlgebra' if 'NormalizationAlgebra' in path.name else
                 'ExactLiouvilleComparison.NormalizationSqrt' if 'NormalizationSqrt' in path.name else NS)
    source_decls += [namespace + '.' + n for n in re.findall(r'^(?:@\[simp\] )?(?:def|abbrev|lemma|theorem|structure) ([^\s({]+)', source, re.M)]
inputs = sorted(set(modules + list(OUT.glob('*.lean')) +
    list(Path('docs').glob('cylindrical-compatibility-normalization*.md')) +
    list(Path('docs').glob('normalization-algebra*.md')) + list(Path('docs').glob('normalization-sqrt*.md')) + [Path(p) for p in (
    'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'docs/objective.md',
    'ExactLiouvilleComparison/Geometry.lean',
    'docs/reference/exact_liouville_comparison.tex', 'scripts/verify-cylindrical-compatibility-normalization.py')] +
    list(OUT.glob('*review.md'))))
before = {str(p): digest(p) for p in inputs}
checks = []
with tempfile.TemporaryDirectory(prefix='normalization-bundle-', dir=os.environ.get('TMPDIR', '/tmp')) as tmp:
    scratch = Path(tmp)
    logs = {}
    for label, args, output, marker in [
        ('build', ['ExactLiouvilleComparison.CylindricalCompatibilityNormalizationConsumers'], None, None),
        ('inventory', ['--lean', str(OUT / 'CylindricalCompatibilityNormalizationInventory.lean')], 'types.txt', 'NORMALIZATION_BUNDLE_INVENTORY_COMPLETE'),
        ('axioms', ['--lean', str(OUT / 'CylindricalCompatibilityNormalizationAxioms.lean')], 'axioms.tsv', 'NORMALIZATION_BUNDLE_AXIOMS_COMPLETE'),
    ]:
        env = dict(os.environ)
        if output:
            env['NORMALIZATION_BUNDLE_AUDIT_OUTPUT'] = str(scratch / output)
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
inventory_bytes = (OUT / 'types.txt').read_bytes()
(OUT / 'types.txt.gz.base64').write_bytes(base64.b64encode(gzip.compress(inventory_bytes, mtime=0)) + b'\n')
assert gzip.decompress(base64.b64decode((OUT / 'types.txt.gz.base64').read_bytes())) == inventory_bytes
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
(OUT / 'final-receipt.json').write_text(json.dumps({
    'scope': 'Actual native smooth compatible normalization from supplied metric, arbitrary finite rank and empty base, fiberwise recovery, arbitrary-frame naturality, native tangent consumers. Cylindrical extension is outside this prerequisite.',
    'mission': '50754190-03fe-44b3-830e-5b109eca0470',
    'source_sha256': before, 'pins': pins, 'checks': checks,
    'source_declarations': source_decls, 'environment_declaration_count': len(names),
    'axioms': axioms, 'allowed_axioms': sorted(ALLOWED),
    'uncompressed_inventory_sha256': hashlib.sha256(inventory_bytes).hexdigest(),
    'uncompressed_inventory_bytes': len(inventory_bytes),
    'generated_sha256': {str(OUT / p): digest(OUT / p) for p in ('types.txt.gz.base64', 'types.txt.names', 'axioms.tsv')},
}, indent=2) + '\n')
print(f'Verified native bundle normalization: {len(names)} elaborated declarations, allowed-only transitive axioms.')
