#!/usr/bin/env python3
"""Managed source-bound validation of the partial cylindrical compatibility prerequisites."""
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
OUT = ROOT / 'verification/cylindrical-compatibility'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MODULES = ['CylindricalCompatibilityStatement', 'CylindricalCompatibilityBridges',
           'CylindricalCompatibilityEndAlgebra', 'CylindricalCompatibilityEndForm',
           'CylindricalCompatibilityEndTransport', 'CylindricalCompatibilityRelativeSection',
           'CylindricalCompatibilityChecks']
PINS = {'fsfltz': '1a3d387cfacc746e25aad31e5b27b1803103e7cb',
        'mathlib': 'd13f23b723b8a846827a245b89c10fc7d3f11612'}
BASE = '24b8ee9589e80d6e415cf978e895cc33338deeb3'

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    os.chdir(ROOT)
    for p,h in json.loads((OUT/'base-bindings.json').read_text()).items():
        assert digest(p)==h, ('Accepted source changed',p)
    for p,h in json.loads((OUT/'statement-hashes.json').read_text()).items():
        assert digest(p)==h, ('Reviewed statement changed',p)
    manifest=json.loads(Path('lake-manifest.json').read_text())
    pins={p['name']:p['rev'] for p in manifest['packages']}
    assert pins.items() >= PINS.items()
    for package in manifest['packages']:
        p=Path('.lake/packages')/package['name']
        assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==package['rev']
        subprocess.run(['git','-C',str(p),'diff','--exit-code','HEAD'],check=True,capture_output=True)
    declarations=[]
    for m in MODULES:
        p=Path('ExactLiouvilleComparison')/(m+'.lean');s=p.read_text()
        assert not re.search(r'\b(sorry|sorryAx|admit|axiom|unsafe|opaque)\b',s),str(p)
        ns='ExactLiouvilleComparison.CylindricalCompatibility'
        for line in s.splitlines():
            if line.startswith('namespace '):
                name=line.split()[1]
                ns=name if name.startswith('ExactLiouvilleComparison') else ns+'.'+name
            match=re.match(r'^(?:@\[simp\] )?(def|abbrev|theorem|structure) (\S+)',line)
            if match:declarations.append({'path':str(p),'kind':match[1],'name':ns+'.'+match[2]})
    inputs={str(p) for p in Path('ExactLiouvilleComparison').glob('*.lean')}
    inputs|={str(p.relative_to(ROOT)) for p in OUT.glob('*') if p.is_file() and p.suffix in {'.lean','.json','.md'}}
    inputs|={'lean-toolchain','lakefile.toml','lake-manifest.json','docs/objective.md',
             'docs/reference/exact_liouville_comparison.tex','docs/cylindrical-compatibility-crosswalk.md',
             'docs/cylindrical-compatibility-progress.md','scripts/verify-cylindrical-compatibility.py'}
    before={p:digest(p) for p in sorted(inputs)}
    scratch=Path(tempfile.mkdtemp(prefix='cylindrical-compatibility-check-',dir=os.environ.get('TMPDIR')))
    env=dict(os.environ,CYLINDRICAL_COMPATIBILITY_AUDIT_DIR=str(scratch))
    checks=[]
    for label,args,marker in [
        ('build',['ExactLiouvilleComparison.CylindricalCompatibilityChecks'],None),
        ('audit',['--lean','verification/cylindrical-compatibility/Audit.lean'],'CYLINDRICAL_COMPATIBILITY_AUDIT_COMPLETE'),
        ('consumers',['--lean','ExactLiouvilleComparison/CylindricalCompatibilityChecks.lean'],'CYLINDRICAL_COMPATIBILITY_CONSUMERS_COMPLETE')]:
        command=['horizon-lean-check']+args
        with (scratch/(label+'.txt')).open('w') as f:
            p=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,env=env,text=True)
        log=(scratch/(label+'.txt')).read_text()
        if p.returncode:
            print(log);raise SystemExit(p.returncode)
        receipt=json.loads([l for l in log.splitlines() if l.startswith('{')][-1])
        assert receipt['ok'] and receipt['snapshot_verified'],receipt
        if marker:assert marker in log.splitlines(),marker
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
    required=['ExactLiouvilleComparison.CylindricalCompatibility.endTangentJ_square',
              'ExactLiouvilleComparison.CylindricalCompatibility.endTangentJ_invariant',
              'ExactLiouvilleComparison.CylindricalCompatibility.endTangentJ_positive',
              'ExactLiouvilleComparison.CylindricalCompatibility.end_twoForm',
              'ExactLiouvilleComparison.CylindricalCompatibility.comparison_of_extends',
              'ExactLiouvilleComparison.CylindricalCompatibility.RelativeSection.exists_relative_section',
              'ExactLiouvilleComparison.FiniteTypeComparison.finiteTypeTarget']
    assert set(required)<=set(names)
    # Lean's actual imported-module inventory supplies the full non-core source closure.
    roots=[Path('.')] + [Path('.lake/packages')/p['name'] for p in manifest['packages']]
    sources=dict(before);imports=[];toolchain=[]
    for name in (scratch/'modules.txt').read_text().splitlines():
        relative=Path(name.replace('.','/')+'.lean')
        candidates=[root/relative for root in roots if (root/relative).is_file()]
        if not candidates:
            assert name.split('.')[0] in {'Init','Lean','Lake','Std'},name
            toolchain.append(name);continue
        assert len(candidates)==1,(name,candidates)
        p=str(candidates[0]);h=digest(p);sources[p]=h
        imports.append({'module':name,'path':p,'sha256':h})
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
    final=OUT/'progress';final.mkdir(exist_ok=True)
    for p in scratch.iterdir():
        if p.is_dir():shutil.copytree(p,final/p.name,dirs_exist_ok=True)
        else:shutil.copyfile(p,final/p.name)
    (final/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
    (final/'declarations.json').write_text(json.dumps(declarations,indent=2)+'\n')
    (final/'receipt.json').write_text(json.dumps({
        'scope':'PARTIAL: native end algebra/form/pointwise transport, relative convex gluing and conditional consumer bridges; no global existence or extension proof',
        'mission':'deee4e3c-9772-491a-b842-98913f062983','base_commit':BASE,
        'statement_commit':BASE,
        'pins':pins,'source_sha256':sources,'imports':imports,'core_toolchain_modules':toolchain,
        'checks':checks,'required_exports':required,'allowed_axioms':sorted(ALLOWED),
        'source_declaration_count':len(declarations),'elaborated_declaration_count':len(names),
        'elaborated_storage':storage,
        'limitations':['ExistenceTarget, ExtensionTarget and ContactExistenceTarget remain unproved',
          'End tangent transport is pointwise; native section smoothness and core metric gluing remain',
          'Relative section theorem has an explicit local-section premise',
          'Consumer bridges retain the stated unproved construction hypotheses',
          'No final mission review, root/phase acceptance, final packaging or GitHub upload']},indent=2)+'\n')
    print(f'CYLINDRICAL_COMPATIBILITY_VERIFIED: {len(declarations)} source declarations, {len(names)} audited declarations, {len(imports)} source import bindings')

if __name__=='__main__':main()
