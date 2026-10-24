#!/usr/bin/env python3
"""Build the statements/consumers and audit their actual transitive axioms.

Uses managed admission when running under Horizon. Receipts bind source bytes;
they do not assert mathematical fidelity or prove the target propositions.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
source_files = sorted([Path('ExactLiouvilleComparison.lean'),
                       *Path('ExactLiouvilleComparison').glob('*.lean'),
                       Path('verification/AxiomAudit.lean'),
                       Path('verification/ElaboratedStatements.lean'),
                       Path('lakefile.toml'), Path('lake-manifest.json'),
                       Path('lean-toolchain')])
hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files}
for p in source_files:
    if p.suffix == '.lean' and re.search(r'\b(sorry|admit|axiom)\b', p.read_text()):
        raise SystemExit(f'Forbidden admission/declaration token in {p}')

managed = bool(os.environ.get('HORIZON_LEAN_BUILD'))
commands = [
    ['horizon-lean-check', 'ExactLiouvilleComparison', 'ExactLiouvilleComparison.InterfaceChecks']
    if managed else ['lake', 'build', 'ExactLiouvilleComparison', 'ExactLiouvilleComparison.InterfaceChecks'],
    ['horizon-lean-check', '--lean', 'verification/AxiomAudit.lean']
    if managed else ['lake', 'env', 'lean', 'verification/AxiomAudit.lean'],
    ['horizon-lean-check', '--lean', 'verification/ElaboratedStatements.lean']
    if managed else ['lake', 'env', 'lean', 'verification/ElaboratedStatements.lean'],
]
receipts = []
for label, cmd in zip(['build', 'axioms', 'elaborated-statements'], commands):
    result = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / f'{label}.log').write_text(result.stdout)
    receipt = {'command': cmd, 'returncode': result.returncode}
    if managed:
        lines = [x for x in result.stdout.splitlines() if x.startswith('{')]
        if not lines:
            raise SystemExit(f'No managed receipt for {label}; see verification/{label}.log')
        receipt['managed'] = json.loads(lines[-1])
        if not receipt['managed'].get('snapshot_verified'):
            raise SystemExit(f'Unverified snapshot for {label}')
    receipts.append(receipt)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    if label == 'axioms':
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
        reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)]
        if len(reports) != 20:
            raise SystemExit(f'Expected 20 audit reports, got {len(reports)}')
        for name, ax in reports:
            forbidden = set(filter(None, re.split(r'[,\s]+', ax))) - {
                'propext', 'Classical.choice', 'Quot.sound'}
            if forbidden:
                raise SystemExit(f'Forbidden axioms: {name}: {forbidden}')
        receipt['declarations'] = {n: list(filter(None, re.split(r'[,\s]+', a))) for n, a in reports}

if hashes != {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files}:
    raise SystemExit('Source changed during verification')
manifest = json.loads(Path('lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
for package in ['fsfltz', 'mathlib']:
    actual = subprocess.check_output(['git', '-C', f'.lake/packages/{package}', 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == pins[package], (package, actual)
assert hashlib.sha256(Path('docs/reference/exact_liouville_comparison.tex').read_bytes()).hexdigest() == (
    '8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576')
(OUT / 'statement-receipt.json').write_text(json.dumps({
    'scope': 'Statement and definition bridges only; no comparison theorem proved',
    'source_sha256': hashes, 'pins': pins, 'checks': receipts,
}, indent=2) + '\n')
print('Statement, consumers and 20 transitive axiom checks passed; source-byte receipt saved.')
