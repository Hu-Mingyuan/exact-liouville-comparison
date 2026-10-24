#!/usr/bin/env python3
"""Check the unchanged manuscript assembly and exact private prerequisite bindings."""
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
OUT = Path('verification/manuscript-comparison')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MODULES = ['FiniteTypeComparisonStatement', 'ManuscriptComparisonStatement',
           'FiniteTypeComparison', 'ManuscriptComparison', 'ManuscriptComparisonConsumers']
BASE = 'f8b5b6bcb56a18c0094d15fed4619ff100327e30'
PINS = {'mathlib': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
        'fsfltz': '1a3d387cfacc746e25aad31e5b27b1803103e7cb'}

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    bindings = json.loads((OUT/'import-manifest.json').read_text())
    for e in bindings:
        assert digest(e['path']) == e['sha256'], ('Changed imported source', e)
    for p,h in json.loads((OUT/'statement-hashes.json').read_text()).items():
        assert digest(p) == h, ('Changed reviewed statement/definition',p)
    preserved = subprocess.check_output(['git','ls-tree','-r','--name-only',BASE],text=True).splitlines()
    for p in preserved:
        assert Path(p).read_bytes() == subprocess.check_output(['git','show',BASE+':'+p]),p
    receipts = [OUT/'main-receipt.json', Path('verification/corollaries/final/receipt.json'),
                Path('verification/finite-type-radial/receipt.json')]
    dependencies = set()
    for p in receipts:
        r = json.loads(p.read_text())
        for path,h in r['source_sha256'].items():
            assert digest(path)==h, ('Changed prerequisite review binding',str(p),path)
            if path.startswith('.lake/'): dependencies.add(path)
    manifest = json.loads(Path('lake-manifest.json').read_text())
    pins = {p['name']:p['rev'] for p in manifest['packages']}
    assert pins.items() >= PINS.items()
    for pkg in manifest['packages']:
        p = '.lake/packages/'+pkg['name']
        assert subprocess.check_output(['git','-C',p,'rev-parse','HEAD'],text=True).strip()==pkg['rev']
        subprocess.run(['git','-C',p,'diff','--exit-code','HEAD'],check=True,capture_output=True)
    declarations = []
    for module in MODULES:
        p=Path('ExactLiouvilleComparison')/(module+'.lean'); source=p.read_text()
        assert not re.search(r'\b(sorry|sorryAx|admit|axiom|unsafe|opaque)\b',source),str(p)
        ns=re.search(r'^namespace (\S+)',source,re.M).group(1)
        for kind,name in re.findall(r'^(def|abbrev|theorem) (\S+)',source,re.M):
            declarations.append({'path':str(p),'kind':kind,'name':ns+'.'+name})
    sources = set(preserved) | {e['path'] for e in bindings} | dependencies
    sources |= {str(p) for p in Path('ExactLiouvilleComparison').glob('*.lean')}
    sources |= {str(p) for p in receipts} | {str(OUT/n) for n in [
        'Audit.lean','import-manifest.json','statement-hashes.json','statement-review.md',
        'main-final-review.md','corollaries-final-review.md','prerequisite-bindings.json']}
    sources |= {'scripts/verify-manuscript-comparison.py','docs/manuscript-comparison-crosswalk.md',
                'docs/manuscript-comparison-proof.md','verification/finite-type-radial/final-review.md'}
    before={p:digest(p) for p in sorted(sources)}
    checks=[]
    scratch=Path(tempfile.mkdtemp(prefix='manuscript-validation-',dir=os.environ.get('TMPDIR')))
    env=dict(os.environ,MANUSCRIPT_AUDIT_DIR=str(scratch))
    for label,args,marker in [
        ('build',['ExactLiouvilleComparison.ManuscriptComparisonConsumers'],None),
        ('audit',['--lean',str(OUT/'Audit.lean')],'MANUSCRIPT_AUDIT_COMPLETE'),
        ('consumers',['--lean','ExactLiouvilleComparison/ManuscriptComparisonConsumers.lean'],
         'MANUSCRIPT_CONSUMERS_COMPLETE')]:
        command=['horizon-lean-check']+args
        with (scratch/(label+'.txt')).open('w') as f:
            p=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,env=env,text=True)
        log=(scratch/(label+'.txt')).read_text()
        if p.returncode:
            print(log);raise SystemExit(p.returncode)
        receipt=json.loads([l for l in log.splitlines() if l.startswith('{')][-1])
        assert receipt['ok'] and receipt['snapshot_verified'],receipt
        if marker: assert marker in log.splitlines(),marker
        checks.append({'command':command,'managed':receipt})
        print(label+': passed',flush=True)
    assert len({c['managed']['source_key'] for c in checks})==1
    names=(scratch/'names.txt').read_text().splitlines()
    assert len(names)==len(set(names))
    assert {d['name'] for d in declarations} <= set(names)
    axioms={}
    for line in (scratch/'axioms.tsv').read_text().splitlines():
        n,ax=line.split('\t');used=set(filter(None,ax.split(',')))
        assert used<=ALLOWED,(n,used);axioms[n]=sorted(used)
    assert set(axioms)==set(names)
    required=['ExactLiouvilleComparison.FiniteTypeComparison.finiteTypeTarget',
              'ExactLiouvilleComparison.ManuscriptComparison.manuscriptTarget',
              'ExactLiouvilleComparison.ManuscriptComparison.completeLiouvilleComparisonTarget']
    assert set(required)<=set(names)
    storage={}
    for folder in ['types','definitions']:
        storage[folder]={}
        for p in sorted((scratch/folder).glob('*.txt')):
            b=p.read_bytes();assert '⋯' not in b.decode(),str(p)
            sha=hashlib.sha256(b).hexdigest();name=p.stem
            if len(b)>256*1024:
                q=p.with_suffix('.txt.gz');q.write_bytes(gzip.compress(b,mtime=0));p.unlink();p=q
            storage[folder][name]={'path':folder+'/'+p.name,'sha256':digest(p),
                                  'uncompressed_sha256':sha,'uncompressed_bytes':len(b)}
    assert set(storage['types'])==set(names)
    assert before=={p:digest(p) for p in before},'Source drift during validation'
    final=OUT/'final';final.mkdir(exist_ok=True)
    for p in scratch.iterdir():
        if p.is_dir(): shutil.copytree(p,final/p.name,dirs_exist_ok=True)
        else: shutil.copyfile(p,final/p.name)
    (final/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
    (final/'declarations.json').write_text(json.dumps(declarations,indent=2)+'\n')
    (final/'receipt.json').write_text(json.dumps({
        'scope':'Unchanged FiniteTypeTarget and ManuscriptTarget proofs; prescribed complete-Liouville specialization',
        'mission':'7d0fe0b7-a970-4cef-ae30-6b624452f600','pins':pins,
        'source_sha256':before,'checks':checks,'required_exports':required,'allowed_axioms':sorted(ALLOWED),
        'source_declaration_count':len(declarations),'elaborated_declaration_count':len(names),
        'elaborated_storage':storage,'baseline':BASE,
        'coverage_boundary':'Explicit FsFltz Completion and real Cauchy–Riemann embedding presentations; see reviewed crosswalk',
        'excluded':['global acceptance','final packaging/PDFs','GitHub upload']},indent=2)+'\n')
    print(f'MANUSCRIPT_VERIFIED: {len(declarations)} source and {len(names)} elaborated declarations')

if __name__=='__main__':main()
