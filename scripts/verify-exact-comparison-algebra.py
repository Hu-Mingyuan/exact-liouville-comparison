#!/usr/bin/env python3
"""Check only the bounded exact-comparison algebra, its consumers and trust closure."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path('verification/exact-comparison-algebra')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
preserved = json.loads((OUT / 'preserved-inputs.json').read_text())
for path, digest in preserved['sha256'].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest, path
modules = sorted(Path('ExactLiouvilleComparison').glob('ExactComparisonAlgebra*.lean'))
consumers = sorted(OUT.glob('*.lean'))
paths = modules + consumers + [Path('docs/exact-comparison-algebra.md'), Path(__file__).relative_to(ROOT),
    OUT / 'declarations.json', OUT / 'preserved-inputs.json', OUT / 'statement-review.md']

def hashes():
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

inventory = json.loads((OUT / 'declarations.json').read_text())
assert set(n['file'] for n in inventory) == set(map(str, modules))
for n in inventory:
    assert '#check ' + n['name'] + '\n' in (OUT / 'Types.lean').read_text(), n
    assert '#print axioms ' + n['name'] + '\n' in (OUT / 'Axioms.lean').read_text(), n
before = hashes()
for path in modules + consumers:
    assert not re.search(r'\b(sorry|admit|axiom|sorryAx)\b', path.read_text()), path
manifest = json.loads(Path('lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
for name, pin in pins.items():
    installed = subprocess.check_output(['git', '-C', f'.lake/packages/{name}', 'rev-parse', 'HEAD'], text=True).strip()
    assert installed == pin, (name, installed, pin)
checks = [('build', ['ExactLiouvilleComparison.ExactComparisonAlgebra'], None)]
checks += [(p.stem, ['--lean', str(p)], f'EXACT_COMPARISON_{p.stem.upper()}_COMPLETE') for p in consumers]
receipts = []
# Keep outputs outside the checkout until every managed snapshot check finishes.
with tempfile.TemporaryDirectory(prefix='exact-comparison-algebra-') as tmp:
    logs = {}
    for name, args, marker in checks:
        if os.environ.get('HORIZON_LEAN_BUILD'):
            cmd = ['horizon-lean-check', *args]
        elif args[0] == '--lean':
            cmd = ['lake', 'env', 'lean', args[1]]
        else:
            cmd = ['lake', 'build', *args]
        result = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        Path(tmp, name + '.txt').write_text(result.stdout)
        logs[name] = result.stdout
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
        entry = {'command': cmd, 'returncode': result.returncode}
        if os.environ.get('HORIZON_LEAN_BUILD'):
            report = json.loads([l for l in result.stdout.splitlines() if l.startswith('{')][-1])
            assert report['ok'] and report['snapshot_verified'], report
            entry['managed'] = report
        if marker:
            assert marker in result.stdout.splitlines(), marker
            assert 'output truncated' not in result.stdout.lower()
            source = Path(args[-1]).read_text()
            expected = re.findall(r'^#print axioms (\S+)$', source, re.M)
            reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
            reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)]
            assert sorted(n for n, _ in reports) == sorted(expected), (expected, reports)
            entry['axioms'] = {}
            for decl, axioms in reports:
                actual = set(filter(None, re.split(r'[,\s]+', axioms)))
                assert actual <= allowed, (decl, actual)
                entry['axioms'][decl] = sorted(actual)
            for decl in re.findall(r'^#check (\S+)$', source, re.M):
                assert re.search(r'^' + re.escape(decl) + r'(?:\s|[.{:])', result.stdout, re.M), decl
        receipts.append(entry)
    assert hashes() == before, 'Changed sources during validation'
    for name, log in logs.items():
        (OUT / (name + '.txt')).write_text(log)
(OUT / 'receipt.json').write_text(json.dumps({
    'scope': 'Structural exact comparison algebra only; no MainTarget or Moser exactness proof.',
    'source_sha256': before, 'base': preserved['base'], 'pins': pins, 'checks': receipts,
}, indent=2) + '\n')
print('EXACT_COMPARISON_ALGEBRA_VERIFIED')
