#!/usr/bin/env python3
"""Serial managed verification of the isolated third-path scalar prerequisite."""
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path('verification/third-path-exhaustion')
TMP = Path(os.environ['TMPDIR']) / 'third-path-exhaustion-verification'
TMP.mkdir(parents=True, exist_ok=True)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MODULE = Path('ExactLiouvilleComparison/ThirdPathExhaustion.lean')

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

baseline = json.loads((OUT / 'baseline.json').read_text())
for path, expected in baseline['files'].items():
    assert digest(path) == expected, ('Changed accepted source', path)
source = MODULE.read_text()
assert not re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe|opaque)\b', source)
namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
decls = [{'file': str(MODULE), 'kind': kind, 'name': namespace + '.' + name}
         for kind, name in re.findall(r'^(theorem|def|structure|lemma) ([^\s({]+)', source, re.M)]
names = [d['name'] for d in decls]
assert len(names) == 8 and len(set(names)) == 8
(OUT / 'declarations.json').write_text(json.dumps(decls, indent=2) + '\n')
header = 'import ExactLiouvilleComparison.ThirdPathExhaustion\n'
types = header + 'open Lean Elab Command in\nrun_cmd do\n'
types += '  for n in [' + ', '.join('``' + n for n in names) + '] do\n'
types += '''    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    let line := s!"{n} : {ty.pretty}"
    logInfo (s!"SCALAR_TYPE_ASCII {line.toList.map Char.toNat}")
'''
types += '#eval IO.println "THIRD_PATH_SCALAR_TYPES_COMPLETE"\n'
(OUT / 'DeclarationTypes.lean').write_text(types)
(OUT / 'AxiomAudit.lean').write_text(header + '\n'.join('#print axioms ' + n for n in names)
    + '\n#eval IO.println "THIRD_PATH_SCALAR_AXIOMS_COMPLETE"\n')
manifest = json.loads(Path('lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
for pkg in ['mathlib', 'fsfltz']:
    assert subprocess.check_output(['git', '-C', '.lake/packages/' + pkg, 'rev-parse', 'HEAD'],
                                   text=True).strip() == pins[pkg]
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
sources = sorted(set(list(baseline['files']) + [str(MODULE),
    'scripts/verify-third-path-exhaustion.py', str(OUT / 'README.md'),
    str(OUT / 'baseline.json'), str(OUT / 'declarations.json')]
    + [str(p) for p in OUT.glob('*.lean')]))
before = {p: digest(p) for p in sources}
checks = []
for label, args, marker in [
    ('build', ['ExactLiouvilleComparison.ThirdPathExhaustion'], None),
    ('types', ['--lean', str(OUT / 'DeclarationTypes.lean')], 'THIRD_PATH_SCALAR_TYPES_COMPLETE'),
    ('axioms', ['--lean', str(OUT / 'AxiomAudit.lean')], 'THIRD_PATH_SCALAR_AXIOMS_COMPLETE'),
    ('consumer', ['--lean', str(OUT / 'Consumer.lean')], 'THIRD_PATH_SCALAR_CONSUMER_COMPLETE')]:
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
        arrays = re.findall(r'^SCALAR_TYPE_ASCII (\[[^\]]*\])', output, re.M)
        assert len(arrays) == len(names)
        decoded = '\n\n'.join(''.join(chr(i) for i in json.loads(a)) for a in arrays) + '\n'
        assert all(n + ' :' in decoded for n in names)
        (TMP / 'elaborated-types.txt').write_text(decoded)
    if label == 'axioms':
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
        reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", output)]
        assert sorted(n for n, _ in reports) == sorted(names)
        record['declarations'] = {}
        for n, axioms in reports:
            used = set(filter(None, re.split(r'[,\s]+', axioms)))
            assert used <= ALLOWED, (n, used)
            record['declarations'][n] = sorted(used)
    checks.append(record)
    print(label + ': passed', flush=True)
assert before == {p: digest(p) for p in sources}, 'Source changed during verification'
assert len({c['managed']['source_key'] for c in checks}) == 1
for p in TMP.iterdir():
    if p.suffix in ['.log', '.txt']:
        (OUT / p.name).write_bytes(p.read_bytes())
(OUT / 'receipt.json').write_text(json.dumps({
    'scope': 'Third-path sqrt(R) scalar prerequisite only; no field/evolution existence claimed',
    'mission_id': '4c628a59-74bc-4f35-b15d-e0cadf9c4142',
    'integration_owner': '715bfb6e-da34-4a2a-b10b-1821801f6a8a',
    'source_sha256': before, 'pins': pins, 'checks': checks,
    'declaration_count': len(names), 'allowed_axioms': sorted(ALLOWED),
    'remaining_parent_work': ['construct literal third-path field', 'discharge native joint regularity and g norm bound',
                              'construct evolution', 'integration and final review']}, indent=2) + '\n')
print('Verified 8 scalar lemmas, elaborated types, allowed-only transitive audit and interval consumer.')
