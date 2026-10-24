#!/usr/bin/env python3
"""Serial managed exact-source verification for the bounded Stein/common-reference corollaries."""
import hashlib
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = Path('verification/corollaries')
BASE = 'f8b5b6bcb56a18c0094d15fed4619ff100327e30'
PINS = {'mathlib': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
        'fsfltz': '1a3d387cfacc746e25aad31e5b27b1803103e7cb'}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

for item in json.loads((OUT / 'import-manifest.json').read_text()):
    assert digest(item['path']) == item['sha256'], item
for p, sha in json.loads((OUT / 'statement-hashes.json').read_text()).items():
    assert digest(p) == sha, ('Reviewed semantic source changed', p)
base_files = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], text=True).splitlines()
for p in base_files:
    assert Path(p).read_bytes() == subprocess.check_output(['git', 'show', BASE+':'+p]), p
manifest = json.loads(Path('lake-manifest.json').read_text())
assert {p['name']: p['rev'] for p in manifest['packages']}.items() >= PINS.items()
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
for pkg in manifest['packages']:
    p = '.lake/packages/' + pkg['name']
    assert subprocess.check_output(['git', '-C', p, 'rev-parse', 'HEAD'], text=True).strip() == pkg['rev']
    subprocess.run(['git', '-C', p, 'diff', '--exit-code'], check=True, stdout=subprocess.DEVNULL)
modules = [Path('ExactLiouvilleComparison')/name for name in [
    'CorollaryComparisonStatement.lean', 'SteinComparison.lean',
    'CommonReferenceComparison.lean', 'CorollaryComparisonConsumers.lean']]
for p in modules:
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe)\b', p.read_text()), p
sources = sorted(set(base_files + [str(p) for p in Path('ExactLiouvilleComparison').glob('*.lean')] +
    [str(p) for p in modules] + ['scripts/verify-corollaries.py', 'scripts/import-corollary-inputs.py',
    'docs/corollary-comparison-crosswalk.md', 'docs/corollary-comparison-proof.md',
    str(OUT/'Audit.lean'), str(OUT/'statement-review.md'), str(OUT/'statement-hashes.json'), str(OUT/'import-manifest.json')]))
before = {p: digest(p) for p in sources}
checks = []
with tempfile.TemporaryDirectory(prefix='corollaries-', dir=os.environ['TMPDIR']) as tmp:
    temp = Path(tmp)
    env = dict(os.environ, COROLLARIES_AUDIT_DIR=tmp)
    for label, args, marker in [
        ('build', ['ExactLiouvilleComparison.CorollaryComparisonConsumers'], None),
        ('audit', ['--lean', str(OUT/'Audit.lean')], 'COROLLARIES_AUDIT_COMPLETE'),
        ('consumers', ['--lean', 'ExactLiouvilleComparison/CorollaryComparisonConsumers.lean'], 'COROLLARIES_CONSUMERS_COMPLETE')]:
        cmd = ['horizon-lean-check', *args]
        with (temp/(label+'.log')).open('w') as log:
            proc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, env=env, text=True)
        text = (temp/(label+'.log')).read_text()
        if proc.returncode:
            print(text)
            raise SystemExit(proc.returncode)
        receipt = json.loads([l for l in text.splitlines() if l.startswith('{')][-1])
        assert receipt['ok'] and receipt['snapshot_verified'], receipt
        if marker: assert marker in text.splitlines(), (label, 'Missing completion marker')
        checks.append({'command': cmd, 'managed': receipt})
        print(label+': passed', flush=True)
    names = (temp/'names.txt').read_text().splitlines()
    assert names and len(names) == len(set(names))
    required = ['ExactLiouvilleComparison.SteinComparison.packagedSteinTarget',
        'ExactLiouvilleComparison.SteinComparison.steinTarget',
        'ExactLiouvilleComparison.CommonReferenceComparison.commonReferenceTarget',
        'ExactLiouvilleComparison.CommonReferenceComparison.explicitCommonTarget',
        'ExactLiouvilleComparison.SteinComparison.comparisonWitness']
    assert set(required) <= set(names)
    inventory = []
    for source in modules:
        for kind, name in re.findall(r'^(def|abbrev|theorem) ([A-Za-z_][A-Za-z_0-9]*)', source.read_text(), re.M):
            namespace = re.search(r'^namespace (\S+)', source.read_text(), re.M).group(1)
            full = namespace + '.' + name
            assert full in names, ('Missing source declaration', full)
            inventory.append({'file': str(source), 'kind': kind, 'name': full})
    log = (temp/'audit.log').read_text()
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    assert sorted(n for n, _ in reports) == sorted(names), 'Incomplete axiom inventory'
    axioms = {}
    for n, used in reports:
        used = re.sub(r'\.\{[^}]*\}', '', used)
        used = set(filter(None, re.split(r'[,\s]+', used)))
        assert used <= ALLOWED, (n, used)
        axioms[n] = sorted(used)
    for n in names:
        ty = (temp/'types'/(n+'.txt')).read_text()
        assert ty.startswith(n+' :') and '⋯' not in ty, n
    type_hashes = {n: digest(temp/'types'/(n+'.txt')) for n in names}
    # Preserve complete type text while fitting the private API's per-file limit.
    type_storage = {}
    for n in names:
        p = temp/'types'/(n+'.txt')
        if p.stat().st_size > 512 * 1024:
            packed = p.with_suffix('.txt.gz')
            packed.write_bytes(gzip.compress(p.read_bytes(), mtime=0))
            p.unlink()
            p = packed
        type_storage[n] = {'path': 'types/'+p.name, 'sha256': digest(p)}
    assert before == {p: digest(p) for p in sources}, 'Source drift during checks'
    assert len({c['managed']['source_key'] for c in checks}) == 1, 'Snapshot mismatch'
    final = OUT/'final'
    final.mkdir(exist_ok=True)
    for p in temp.iterdir():
        if p.is_dir(): shutil.copytree(p, final/p.name, dirs_exist_ok=True)
        else: shutil.copyfile(p, final/p.name)
    for n, entry in type_storage.items():
        if entry['path'].endswith('.gz'):
            (final/'types'/(n+'.txt')).unlink(missing_ok=True)
    (final/'source-declarations.json').write_text(json.dumps(inventory, indent=2)+'\n')
    (final/'axioms.json').write_text(json.dumps(axioms, indent=2)+'\n')
    (final/'receipt.json').write_text(json.dumps({
        'scope': 'Stein and common-reference corollaries, explicit native witnesses and original metric/growth bridges',
        'mission': 'b518dc8e-9cf8-40a0-b7dd-1199bf9c17a3', 'baseline': BASE,
        'pins': PINS, 'source_sha256': before, 'checks': checks,
        'declarations': names, 'declaration_count': len(names), 'required_exports': required,
        'allowed_axioms': sorted(ALLOWED),
        'type_sha256': type_hashes, 'type_storage': type_storage,
        'exclusions': ['finite-type corollary', 'full objective acceptance', 'final packaging', 'GitHub upload']
    }, indent=2)+'\n')
print('COROLLARIES_VERIFIED')
