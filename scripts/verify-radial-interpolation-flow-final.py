#!/usr/bin/env python3
"""Reproduce the constructed radial flow build, full types and transitive audit."""
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path('verification/radial-interpolation-flow-final')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

base = json.loads((OUT / 'baseline.json').read_text())
for p, h in base['files'].items():
    assert digest(p) == h, ('Changed preserved input', p)

# Reuse the reviewed fully qualified inventories, including nested namespaces.
decls = []
for p in ['verification/radial-interpolation-flow/input-declarations.json',
          'verification/ode-two-barrier/declarations.json']:
    decls.extend(json.loads(Path(p).read_text()))
for n in ['RadialInterpolationFlow', 'RadialInterpolationFlowChecks']:
    p = Path('ExactLiouvilleComparison') / (n + '.lean')
    s = p.read_text()
    ns = re.search(r'^namespace (\S+)', s, re.M).group(1)
    decls.extend({'file': str(p), 'kind': k, 'name': ns + '.' + name}
                 for k, name in re.findall(r'^(def|theorem|structure) ([^\s({]+)', s, re.M))
names = [d['name'] for d in decls]
assert len(names) == len(set(names)), 'Duplicate declaration'
mods = sorted({d['file'] for d in decls})
for p in mods:
    source = Path(p).read_text()
    assert not re.search(r'\b(sorry|sorryAx|admit|axiom|unsafe|opaque)\b', source), p
    actual = sorted(re.findall(r'^(def|theorem|structure) ([^\s({]+)', source, re.M))
    listed = sorted((d['kind'], d['name'].split('.')[-1]) for d in decls if d['file'] == p)
    assert actual == listed, ('Incomplete explicit declaration inventory', p)
(OUT / 'declarations.json').write_text(json.dumps(decls, indent=2) + '\n')
contracts = ['ExactLiouvilleComparison.RadialInterpolationFlow.Target',
             'ExactLiouvilleComparison.ODE.TwoBarrierEvolutionTarget',
             'ExactLiouvilleComparison.FirstPathFlow.Evolution',
             'ExactLiouvilleComparison.ODE.EvolutionPatch']
header = 'import ExactLiouvilleComparison.RadialInterpolationFlowChecks\n'
# Encode pretty-printed elaborated types as ASCII codepoint arrays in Lean itself.
# This prevents the managed stdout transport from splitting multibyte characters.
# The log retains raw arrays and a decoded inventory; no damaged text is repaired.
type_code = header + 'open Lean Elab Command in\nrun_cmd do\n'
type_code += '  for n in [' + ', '.join('``' + n for n in names) + '] do\n'
type_code += '''    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    let line := s!"{n} : {ty.pretty}"
    logInfo m!"RADIAL_TYPE_ASCII {line.toList.map Char.toNat}"
'''
type_code += '  for n in [' + ', '.join('``' + n for n in contracts) + '] do\n'
type_code += '''    let info ← getConstInfo n
    if let .defnInfo v := info then
      let val ← liftTermElabM do PrettyPrinter.ppExpr v.value
      let line := s!"definition {n} := {val.pretty}"
      logInfo m!"RADIAL_TYPE_ASCII {line.toList.map Char.toNat}"
    if let some st := getStructureInfo? (← getEnv) n then
      for field in st.fieldNames do
        if let some proj := getProjFnForField? (← getEnv) n field then
          let pinfo ← getConstInfo proj
          let ty ← liftTermElabM do PrettyPrinter.ppExpr pinfo.type
          let line := s!"{proj} : {ty.pretty}"
          logInfo m!"RADIAL_TYPE_ASCII {line.toList.map Char.toNat}"
'''
type_code += '#eval IO.println "RADIAL_FLOW_FINAL_DECLARATIONTYPES_COMPLETE"\n'
(OUT / 'DeclarationTypes.lean').write_text(type_code)
(OUT / 'AxiomAudit.lean').write_text(header + '\n'.join('#print axioms ' + n for n in names)
    + '\n#eval IO.println "RADIAL_FLOW_FINAL_AXIOMAUDIT_COMPLETE"\n')

manifest = json.loads(Path('lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
for pkg in ['mathlib', 'fsfltz']:
    assert subprocess.check_output(['git', '-C', '.lake/packages/' + pkg,
                                    'rev-parse', 'HEAD'], text=True).strip() == pins[pkg]
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
sources = sorted(set(list(base['files']) + mods + [
    'scripts/verify-radial-interpolation-flow-final.py', 'docs/radial-interpolation-flow-final.md',
    '.github/workflows/radial-interpolation-flow-final.yml', str(OUT / 'baseline.json'),
    str(OUT / 'declarations.json'), str(OUT / 'proof-review.md')]
    + [str(p) for p in OUT.glob('*.lean')]))
before = {p: digest(p) for p in sources}
checks = []
type_inventory = None
managed = bool(os.environ.get('HORIZON_LEAN_BUILD'))
for label, args, marker in [
    ('build', ['ExactLiouvilleComparison.RadialInterpolationFlowChecks'], None),
    ('types', ['--lean', str(OUT / 'DeclarationTypes.lean')], 'RADIAL_FLOW_FINAL_DECLARATIONTYPES_COMPLETE'),
    ('axioms', ['--lean', str(OUT / 'AxiomAudit.lean')], 'RADIAL_FLOW_FINAL_AXIOMAUDIT_COMPLETE')]:
    cmd = (['horizon-lean-check'] + args if managed else
           ['lake', 'env', 'lean', args[1]] if args[0] == '--lean' else ['lake', 'build'] + args)
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (OUT / (label + '.log')).write_text(r.stdout)
    if r.returncode:
        print(r.stdout)
        raise SystemExit(r.returncode)
    assert '\ufffd' not in r.stdout, ('Replacement character in evidence', label)
    record = {'command': cmd, 'returncode': r.returncode}
    if managed:
        record['managed'] = json.loads([s for s in r.stdout.splitlines() if s.startswith('{')][-1])
        assert record['managed']['ok'] and record['managed']['snapshot_verified']
    if marker:
        assert marker in r.stdout.splitlines(), ('Missing completion marker', label)
    if label == 'types':
        arrays = re.findall(r'^RADIAL_TYPE_ASCII (\[[^\]]*\])', r.stdout, re.M)
        decoded = '\n'.join(''.join(chr(i) for i in json.loads(a)) for a in arrays)
        type_inventory = decoded + '\n'
        for n in names:
            assert re.search(r'^' + re.escape(n) + r'(?:\s|[.{:])', decoded, re.M), n
        assert len(arrays) == len(names) + 2 + 11 + 11, 'Missing contract field or definition'
    if label == 'axioms':
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", r.stdout)
        reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", r.stdout)]
        assert sorted(n for n, _ in reports) == sorted(names)
        record['declarations'] = {}
        for n, a in reports:
            axioms = set(filter(None, re.split(r'[,\s]+', a)))
            assert axioms <= ALLOWED, (n, axioms)
            record['declarations'][n] = sorted(axioms)
    checks.append(record)
assert before == {p: digest(p) for p in sources}, 'Source changed during check'
if managed:
    assert len({c['managed']['source_key'] for c in checks}) == 1
(OUT / 'elaborated-types.txt').write_text(type_inventory)
(OUT / 'receipt.json').write_text(json.dumps({
    'scope': 'Full unchanged radial interpolation flow target, full generic two-barrier evolution, '
             'and unconditional native, zero/unit, k/A, 1/A, equal-identity, critical-fixed and endpoint consumers.',
    'proved_target': 'ExactLiouvilleComparison.RadialInterpolationFlow.radialInterpolationFlow',
    'input_commit': base['input_commit'], 'child_commit': base['child_commit'],
    'source_sha256': before, 'pins': pins, 'checks': checks, 'declaration_count': len(names),
    'contract_prints': contracts, 'allowed_axioms': sorted(ALLOWED),
    'remaining_flow_prerequisites': [],
    'root_scope_retained': ['third path', 'Cartan exactness', 'comparison/corollaries', 'overall acceptance']
}, indent=2) + '\n')
print('Verified full radial interpolation flow;', len(names), 'declarations; allowed-only audit.')
