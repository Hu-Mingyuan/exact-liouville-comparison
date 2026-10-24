#!/usr/bin/env python3
"""Serial exact-source verification of the bounded native Moser regularity delivery."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path('verification/moser-regularity')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

inputs = json.loads((OUT / 'inputs.json').read_text())
for p, record in inputs['files'].items():
    assert digest(p) == record['sha256'], ('Imported source changed', p)
for p, h in json.loads((OUT / 'preserved.json').read_text()).items():
    assert digest(p) == h, ('Preserved source changed', p)
for p, record in json.loads((OUT / 'base-integration.json').read_text())['files'].items():
    assert digest(p) == record['sha256'], ('Base source changed', p)
assert digest('ExactLiouvilleComparison/Geometry.lean') == '2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326'
assert digest('ExactLiouvilleComparison/Statement.lean') == 'ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7'
manifest = json.loads(Path('lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
for package in ('mathlib', 'fsfltz'):
    assert subprocess.check_output(['git', '-C', f'.lake/packages/{package}',
        'rev-parse', 'HEAD'], text=True).strip() == pins[package]
new_modules = sorted(Path('ExactLiouvilleComparison').glob('MoserRegularity*.lean'))
actual = []
for p in new_modules:
    s = p.read_text()
    ns = re.search(r'^namespace (\S+)', s, re.M).group(1)
    actual += [{'file': str(p), 'kind': kind, 'name': ns + '.' + name}
               for kind, name in re.findall(r'^(def|theorem) ([^\s({]+)', s, re.M)]
assert actual == json.loads((OUT / 'declarations.json').read_text())
names = [d['name'] for d in actual]
source_files = sorted(set(list(Path('ExactLiouvilleComparison').glob('*.lean')) +
    [Path('ExactLiouvilleComparison.lean'), Path('lakefile.toml'), Path('lake-manifest.json'),
     Path('lean-toolchain'), Path('docs/reference/exact_liouville_comparison.tex'),
     Path('docs/objective.md'), Path('docs/moser-regularity.md'),
     Path('scripts/verify-moser-regularity.py')] + list(OUT.glob('*.lean')) +
    [p for p in OUT.glob('*.md') if p.name != 'plan.md'] + [OUT / p for p in
      ('inputs.json', 'preserved.json', 'base-integration.json', 'declarations.json')]))
for p in source_files:
    if p.suffix == '.lean':
        assert not re.search(r'\b(sorry|sorryAx|admit|axiom)\b', p.read_text()), p
before = {str(p): digest(p) for p in source_files}
managed = bool(os.environ.get('HORIZON_LEAN_BUILD'))
commands = [
    ('build', ['ExactLiouvilleComparison.MoserRegularityChecks'], None),
    ('types', ['--lean', str(OUT / 'Types.lean')], 'MOSER_REGULARITY_TYPES_COMPLETE'),
    ('axioms', ['--lean', str(OUT / 'AxiomAudit.lean')], 'MOSER_REGULARITY_AXIOMS_COMPLETE'),
]
receipts = []
for label, args, marker in commands:
    cmd = (['horizon-lean-check', *args] if managed else
           ['lake', 'env', 'lean', args[1]] if args[0] == '--lean' else ['lake', 'build', *args])
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (OUT / f'{label}.log').write_text(result.stdout)
    record = {'command': cmd, 'returncode': result.returncode}
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    if managed:
        lines = [s for s in result.stdout.splitlines() if s.startswith('{')]
        record['managed'] = json.loads(lines[-1])
        assert record['managed']['ok'] and record['managed']['snapshot_verified'], record
    if marker:
        assert marker in result.stdout.splitlines(), ('Missing marker', label)
        assert 'output truncated' not in result.stdout.lower()
        assert 'Further build output omitted' not in result.stdout
        assert len(result.stdout.encode()) < 250_000, ('Oversized output', label)
    if label == 'types':
        for n in names:
            assert re.search(r'^' + re.escape(n) + r'(?:\s|[.{:])', result.stdout, re.M), n
        record['elaborated_declarations'] = names
    if label == 'axioms':
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
        reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)]
        assert sorted(n for n, _ in reports) == sorted(names)
        record['declarations'] = {}
        for n, ax in reports:
            axioms = set(filter(None, re.split(r'[,\s]+', ax)))
            assert axioms <= ALLOWED, (n, axioms)
            record['declarations'][n] = sorted(axioms)
    receipts.append(record)
assert before == {str(p): digest(p) for p in source_files}, 'Sources changed during verification'
if managed:
    assert len({r['managed']['source_key'] for r in receipts}) == 1, 'Different source snapshots'
(OUT / 'receipt.json').write_text(json.dumps({
    'scope': 'Bounded inverse contraction, joint native Moser regularity and compact/global scalar bounds only; no flows/comparison/phase acceptance.',
    'source_sha256': before, 'pins': pins, 'checks': receipts,
    'declaration_count': len(names), 'allowed_axioms': sorted(ALLOWED),
    'statement_review': 'verification/moser-regularity/statement-review.md',
    'proof_crosswalk_review': 'verification/moser-regularity/proof-crosswalk-review.md',
}, indent=2) + '\n')
print(f'Moser regularity checks passed: {len(names)} declaration types and transitive axiom reports.')
