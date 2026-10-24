#!/usr/bin/env python3
"""Source-bound managed checks of native finite-interval existence and transitive axioms."""
import hashlib, json, os, re, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path('verification/ode-continuation')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base = json.loads((OUT/'base-source.json').read_text())
for p, h in base['files'].items():
    assert digest(p) == h, ('Changed input', p)
mods = [Path('ExactLiouvilleComparison')/(n+'.lean') for n in
        ['ODEContinuationCutoff', 'ODEContinuation']]
decls = []
for p in mods:
    s = p.read_text()
    ns = re.search(r'^namespace (\S+)', s, re.M).group(1)
    assert not re.search(r'\b(sorry|sorryAx|admit|axiom)\b', s), p
    decls += [{'file': str(p), 'kind': k, 'name': ns+'.'+n} for k, n in
              re.findall(r'^(def|structure|theorem) ([^\s({]+)', s, re.M)]
names = [x['name'] for x in decls]
assert 'ExactLiouvilleComparison.ODE.finiteIntervalExistence' in names
(OUT/'declarations.json').write_text(json.dumps(decls, indent=2)+'\n')
for label, cmd in [('Types', '#check'), ('AxiomAudit', '#print axioms')]:
    extra = ''
    if label == 'Types':
        extra = '''#print ExactLiouvilleComparison.ODE.FiniteIntervalExistenceTarget
example {d : ℕ} {M : FsFltz.Geometry.SmoothManifold d} :
    ExactLiouvilleComparison.ODE.FiniteIntervalExistenceTarget (M := M) :=
  ExactLiouvilleComparison.ODE.finiteIntervalExistence
'''
    (OUT/(label+'.lean')).write_text('import ExactLiouvilleComparison.ODEContinuation\n'+
        '\n'.join(cmd+' '+n for n in names)+'\n'+extra+
        '#eval IO.println "ODE_CONTINUATION_'+label.upper()+'_COMPLETE"\n')
manifest = json.loads(Path('lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz'] == '1a3d387cfacc746e25aad31e5b27b1803103e7cb'
for pkg in ['mathlib', 'fsfltz']:
    assert subprocess.check_output(['git', '-C', '.lake/packages/'+pkg,
        'rev-parse', 'HEAD'], text=True).strip() == pins[pkg]
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
sources = sorted(set(mods + [Path('scripts/verify-ode-continuation.py'),
    Path('docs/ode-continuation.md'), Path('lakefile.toml'), Path('lake-manifest.json'),
    Path('lean-toolchain')] + list(OUT.glob('*.lean')) + list(OUT.glob('*.md')) +
    [OUT/'base-source.json', OUT/'declarations.json'] + [Path(p) for p in base['files']]))
before = {str(p): digest(p) for p in sources}
checks = []
managed = bool(os.environ.get('HORIZON_LEAN_BUILD'))
for label, args, marker in [
    ('build', ['ExactLiouvilleComparison.ODEContinuation'], None),
    ('types', ['--lean', str(OUT/'Types.lean')], 'ODE_CONTINUATION_TYPES_COMPLETE'),
    ('axioms', ['--lean', str(OUT/'AxiomAudit.lean')], 'ODE_CONTINUATION_AXIOMAUDIT_COMPLETE')]:
    cmd = (['horizon-lean-check']+args if managed else
           ['lake', 'env', 'lean', args[1]] if args[0] == '--lean' else ['lake', 'build']+args)
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (OUT/(label+'.log')).write_text(r.stdout)
    if r.returncode:
        print(r.stdout)
        raise SystemExit(r.returncode)
    record = {'command': cmd, 'returncode': r.returncode}
    if managed:
        record['managed'] = json.loads([s for s in r.stdout.splitlines() if s.startswith('{')][-1])
        assert record['managed']['ok'] and record['managed']['snapshot_verified']
    if marker: assert marker in r.stdout.splitlines(), ('Missing output', label)
    if label == 'types':
        for n in names: assert re.search(r'^'+re.escape(n)+r'(?:\s|[.{:])', r.stdout, re.M), n
    if label == 'axioms':
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", r.stdout)
        reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", r.stdout)]
        assert sorted(n for n, _ in reports) == sorted(names)
        record['declarations'] = {}
        for n, a in reports:
            ax = set(filter(None, re.split(r'[,\s]+', a)))
            assert ax <= ALLOWED, (n, ax)
            record['declarations'][n] = sorted(ax)
    checks.append(record)
assert before == {str(p): digest(p) for p in sources}, 'Source changed during check'
if managed: assert len({c['managed']['source_key'] for c in checks}) == 1
(OUT/'receipt.json').write_text(json.dumps({
    'scope': 'Generic finite-interval native curve existence only; no parent evolution or comparison acceptance.',
    'target': 'ExactLiouvilleComparison.ODE.FiniteIntervalExistenceTarget',
    'proof': 'ExactLiouvilleComparison.ODE.finiteIntervalExistence',
    'base_commit': base['commit'], 'source_sha256': before, 'pins': pins, 'checks': checks,
    'declaration_count': len(names), 'allowed_axioms': sorted(ALLOWED)}, indent=2)+'\n')
print('Verified', len(names), 'declarations, including the exact finite-interval existence theorem.')
