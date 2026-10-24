#!/usr/bin/env python3
"""Verify bounded pointwise radial interpolation; no flow or comparison theorem claim."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / 'verification/radial-interpolation'
DECLARATIONS = json.loads((OUT / 'declarations.json').read_text())
BASE = json.loads((OUT / 'base-source.json').read_text())
NEW = sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'ExactLiouvilleComparison').glob('RadialInterpolation*.lean'))
SOURCES = [Path(p) for p in list(BASE) + NEW + [
    'verification/radial-interpolation/base-source.json',
    'verification/radial-interpolation/AxiomAudit.lean',
    'verification/radial-interpolation/Types.lean',
    'verification/radial-interpolation/declarations.json',
    'scripts/verify-radial-interpolation.py',
    'docs/radial-interpolation.md',
    'verification/radial-interpolation/crosswalk-assessment.md']]
def hashes():
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in SOURCES}
source_hashes = hashes()
accepted = {p: v['sha256'] for p, v in BASE.items()}
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
targets = ['ExactLiouvilleComparison.RadialInterpolationChecks']
commands = [('build', ['horizon-lean-check', *targets] if managed else ['lake', 'build', *targets])]
for label, file in [('axioms', 'AxiomAudit.lean'), ('types', 'Types.lean')]:
    path = 'verification/radial-interpolation/' + file
    commands.append((label, ['horizon-lean-check', '--lean', path] if managed else ['lake', 'env', 'lean', path]))
checks = []
# Do not mutate the fingerprinted checkout while a managed check runs.
with tempfile.TemporaryDirectory(prefix='interpolation-verification-') as scratch:
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
    'scope': 'Proved convex radial interpolation, constructed symplectic differential and unique pointwise Moser vectors, energy/radial/Q directional inequalities, native scalar derivatives and uniform exhaustion; no flow, field smoothness or compact-core uniform bound.',
    'accepted_base_commit': '46fccea69cb9524882bbeda83b0ac2067d22a149',
    'accepted_statement_review_artifact': '8930b2e3-ab88-498e-8a6f-d3f732fa8f95',
    'radial_parent_commit': 'b4585587a039a28362ab46285ccd3fe98f4655e1',
    'statement_receipt_companion': 'dcd522c772885851078216fedcff18e00c3b1b7d',
    'source_sha256': source_hashes, 'pins': pins, 'checks': checks,
    'declarations': DECLARATIONS,
}, indent=2) + '\n')
print(f'Bounded module and consumer passed; {len(DECLARATIONS)} transitive audits and complete types saved.')
