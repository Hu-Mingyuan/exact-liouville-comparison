#!/usr/bin/env python3
"""Serial managed checks for the bounded real-matrix square-root theorem."""
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path('verification/normalization-sqrt')
TMP = Path(os.environ['TMPDIR']) / 'normalization-sqrt-verification'
TMP.mkdir(parents=True, exist_ok=True)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MODULE = 'ExactLiouvilleComparison.CylindricalCompatibilityNormalizationSqrt'
SOURCES = sorted(Path('ExactLiouvilleComparison').glob('CylindricalCompatibilityNormalizationSqrt*.lean'))

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

decls = []
for path in SOURCES:
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe|opaque)\b', source), path
    ns = re.search(r'^namespace (\S+)', source, re.M).group(1)
    decls += [{'file': str(path), 'kind': kind, 'name': ns + '.' + name}
              for kind, name in re.findall(r'^(?:@\[[^\]]*\] )?(theorem|def|lemma) ([^\s({]+)', source, re.M)]
names = [d['name'] for d in decls]
assert len(names) == 19 and len(set(names)) == 19, names
(OUT / 'declarations.json').write_text(json.dumps(decls, indent=2) + '\n')
header = 'import ' + MODULE + '\n'
types = header + 'open Lean Elab Command in\nrun_cmd do\n'
types += '  for n in [' + ', '.join('``' + n for n in names) + '] do\n'
types += '''    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    let line := s!"{n} : {ty.pretty}"
    logInfo (s!"SQRT_TYPE_ASCII {line.toList.map Char.toNat}")
'''
types += '#eval IO.println "NORMALIZATION_SQRT_TYPES_COMPLETE"\n'
(OUT / 'DeclarationTypes.lean').write_text(types)
(OUT / 'AxiomAudit.lean').write_text(header + '\n'.join('#print axioms ' + n for n in names)
    + '\n#eval IO.println "NORMALIZATION_SQRT_AXIOMS_COMPLETE"\n')
manifest = json.loads(Path('lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
for pkg in ['mathlib', 'fsfltz']:
    assert subprocess.check_output(['git', '-C', '.lake/packages/' + pkg, 'rev-parse', 'HEAD'],
                                   text=True).strip() == pins[pkg]
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
files = SOURCES + [Path('scripts/verify-normalization-sqrt.py'),
    Path('docs/normalization-sqrt-crosswalk.md'), Path('docs/normalization-sqrt-proof.md'),
    OUT / 'statement-review.md', OUT / 'declarations.json'] + sorted(OUT.glob('*.lean'))
before = {str(p): digest(p) for p in files}
checks = []
for label, args, marker in [
    ('build', [MODULE], None),
    ('types', ['--lean', str(OUT / 'DeclarationTypes.lean')], 'NORMALIZATION_SQRT_TYPES_COMPLETE'),
    ('axioms', ['--lean', str(OUT / 'AxiomAudit.lean')], 'NORMALIZATION_SQRT_AXIOMS_COMPLETE'),
    ('consumer', ['--lean', str(OUT / 'Consumer.lean')], 'NORMALIZATION_SQRT_CONSUMERS_COMPLETE')]:
    cmd = ['horizon-lean-check'] + args
    log = TMP / (label + '.log')
    with log.open('w') as handle:
        result = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT, text=True)
    output = log.read_text()
    if result.returncode:
        print(output)
        raise SystemExit(result.returncode)
    managed = json.loads([line for line in output.splitlines() if line.startswith('{')][-1])
    assert managed['ok'] and managed['snapshot_verified'], managed
    record = {'command': cmd, 'returncode': result.returncode, 'managed': managed}
    if marker:
        assert marker in output.splitlines(), ('Missing completion marker', label)
    if label == 'types':
        arrays = re.findall(r'^SQRT_TYPE_ASCII (\[[^\]]*\])', output, re.M)
        assert len(arrays) == len(names)
        decoded = '\n\n'.join(''.join(chr(i) for i in json.loads(a)) for a in arrays) + '\n'
        assert all(n + ' :' in decoded for n in names)
        (TMP / 'elaborated-types.txt').write_text(decoded)
    if label == 'axioms':
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
        reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", output)]
        assert sorted(n for n, _ in reports) == sorted(names)
        record['declarations'] = {}
        for name, axioms in reports:
            used = set(filter(None, re.split(r'[,\s]+', axioms)))
            assert used <= ALLOWED, (name, used)
            record['declarations'][name] = sorted(used)
    checks.append(record)
    print(label + ': passed', flush=True)
assert before == {str(p): digest(p) for p in files}, 'Source changed during verification'
assert len({c['managed']['source_key'] for c in checks}) == 1
for p in TMP.iterdir():
    if p.suffix in ['.log', '.txt']:
        (OUT / p.name).write_bytes(p.read_bytes())
(OUT / 'receipt.json').write_text(json.dumps({
    'scope': 'Smooth positive-definite real matrix square root; not bundle normalization',
    'mission_id': '226d751b-2331-4986-a5b5-fbbc2f95df01',
    'integration_owner': '1f45f2d4-0edc-4d6b-8646-2c1212915b09',
    'source_sha256': before, 'pins': pins, 'checks': checks,
    'declaration_count': len(names), 'allowed_axioms': sorted(ALLOWED)}, indent=2) + '\n')
print('Verified 19 declarations, types, allowed-only transitive audit, and matrix consumers.')
