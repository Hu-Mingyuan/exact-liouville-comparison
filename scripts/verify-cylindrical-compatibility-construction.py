#!/usr/bin/env python3
"""Managed reproducible check of cylindrical existence, prescribed extension and consumers."""
import gzip, hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/cylindrical-compatibility'
ALLOWED={'propext','Classical.choice','Quot.sound'}
PREFIX='ExactLiouvilleComparison.CylindricalCompatibility'
MODULES=['FormBridge','TransportSmooth','ProductSmooth','MetricPairing','BasinSmooth','Extension','','FinalChecks']
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 os.chdir(ROOT)
 for name in ['base-bindings.json','statement-hashes.json']:
  for p,h in json.loads((OUT/name).read_text()).items():assert digest(p)==h,('Preserved input changed',p)
 manifest=json.loads(Path('lake-manifest.json').read_text());pins={p['name']:p['rev'] for p in manifest['packages']}
 assert pins['mathlib']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
 assert pins['fsfltz']=='1a3d387cfacc746e25aad31e5b27b1803103e7cb'
 for pkg in manifest['packages']:
  p=Path('.lake/packages')/pkg['name']
  assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==pkg['rev']
  subprocess.run(['git','-C',str(p),'diff','--exit-code','HEAD'],check=True,capture_output=True)
 for m in MODULES:
  p=Path('ExactLiouvilleComparison')/('CylindricalCompatibility'+m+'.lean')
  assert not re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe)\b',p.read_text()),p
 inputs=set(Path('ExactLiouvilleComparison').glob('*.lean'))|{
  Path('lean-toolchain'),Path('lakefile.toml'),Path('lake-manifest.json'),
  Path('docs/objective.md'),Path('docs/reference/exact_liouville_comparison.tex'),
  Path('docs/cylindrical-compatibility-crosswalk.md'),Path('docs/cylindrical-compatibility-construction.md'),
  Path(__file__).relative_to(ROOT),OUT/'ConstructionAudit.lean'}
 inputs|=set((OUT/'continuation').glob('*-import.json'))
 before={str(p.relative_to(ROOT) if p.is_absolute() else p):digest(p) for p in sorted(inputs)}
 work=Path(tempfile.mkdtemp(prefix='cylindrical-construction-',dir=os.environ.get('TMPDIR')))
 print('Evidence work directory:',work,flush=True)
 env=dict(os.environ,CYLINDRICAL_CONSTRUCTION_AUDIT_DIR=str(work));checks=[]
 for label,args,marker in [
  ('build',[PREFIX+'FinalChecks',PREFIX+'ContactBundleAudit'],None),
  ('audit',['--lean',str((OUT/'ConstructionAudit.lean').relative_to(ROOT))],'CYLINDRICAL_CONSTRUCTION_AUDIT_COMPLETE'),
  ('consumers',['--lean','ExactLiouvilleComparison/CylindricalCompatibilityFinalChecks.lean'],'CYLINDRICAL_COMPATIBILITY_FINAL_CONSUMERS_COMPLETE')]:
  cmd=['horizon-lean-check',*args]
  with (work/(label+'.log')).open('w') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
  log=(work/(label+'.log')).read_text()
  if r.returncode:print(log);raise SystemExit(r.returncode)
  receipt=json.loads([l for l in log.splitlines() if l.startswith('{')][-1])
  assert receipt['ok'] and receipt['snapshot_verified'],receipt
  if marker:assert marker in log.splitlines(),marker
  checks.append({'command':cmd,'managed':receipt});print(label+': passed',flush=True)
 assert len({c['managed']['source_key'] for c in checks})==1
 names=(work/'names.txt').read_text().splitlines();inventory=(work/'inventory.txt').read_text().splitlines()
 assert len(names)==len(set(names)) and set(inventory)<=set(names)
 required=[PREFIX+'.'+n for n in ['extensionTarget','existenceTarget','consumerTarget',
  'extension_of_prescribed_kernel','FinalChecks.native_consumer','contactExistenceTarget']]
 assert set(required)<=set(names)
 assert set(required)-{PREFIX+'.contactExistenceTarget'}<=set(inventory)
 axioms={}
 for l in (work/'axioms.tsv').read_text().splitlines():
  n,ax=l.split('\t');used=set(filter(None,ax.split(',')));assert used<=ALLOWED,(n,used);axioms[n]=sorted(used)
 assert set(axioms)==set(names)
 raw=(work/'declarations.jsonl').read_bytes();records=[json.loads(l) for l in raw.splitlines()]
 decls=[r for r in records if 'declaration' in r];nodes=[r for r in records if 'node' in r]
 assert [r['display_name'] for r in decls]==inventory
 assert [r['node'] for r in nodes]==list(range(len(nodes)))
 for r in decls:
  assert 'level_params' in r
  if r.get('encoding')=='native-repr':
   s=(work/r['raw_path']).read_text();assert s.startswith('DECL '+r['display_name']+'\nNAME_EXPR ')
   assert '\nLEVEL_PARAMS ' in s and '\nTYPE_EXPR ' in s and '⋯' not in s
  else:
   assert isinstance(r['type_root'],int) and 0<=r['type_root']<len(nodes)
   assert r['value_root'] is None or 0<=r['value_root']<len(nodes)
 compressed=gzip.compress(raw,mtime=0);assert gzip.decompress(compressed)==raw
 (work/'declarations.jsonl.gz').write_bytes(compressed)
 sources=dict(before);imports=[];toolchain=[];core_sources={}
 version=Path('lean-toolchain').read_text().strip().split(':v')[-1]
 core_root=Path('/opt/lean')/('lean-'+version+'-linux')/'src/lean'
 roots=[Path('.')]+[Path('.lake/packages')/p['name'] for p in manifest['packages']]
 for name in (work/'modules.txt').read_text().splitlines():
  rel=Path(name.replace('.','/')+'.lean');candidates=[r/rel for r in roots if (r/rel).is_file()]
  if not candidates:
   assert name.split('.')[0] in {'Init','Lean','Std','Lake'},name
   core=(core_root/'lake'/rel) if name.startswith('Lake.') else core_root/rel
   assert core.is_file(),core
   core_sources[str(core)]=digest(core);toolchain.append(name);continue
  assert len(candidates)==1,(name,candidates)
  p=str(candidates[0]);sources[p]=digest(p);imports.append({'module':name,'path':p,'sha256':sources[p]})
 assert before=={p:digest(p) for p in before},'Source drift'
 (work/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
 artifacts={str(p.relative_to(work)):digest(p) for p in work.rglob('*') if p.is_file()}
 result={'scope':'Unconditional cylindrical existence, arbitrary prescribed smooth contact-end extension and original native comparison consumer',
  'mission':'deee4e3c-9772-491a-b842-98913f062983','mission_revision':8,
  'reviewed_statement_commit':'24b8ee9589e80d6e415cf978e895cc33338deeb3',
  'pins':pins,'toolchain':Path('lean-toolchain').read_text().strip(),
  'source_sha256':sources,'imports':imports,'core_toolchain_modules':toolchain,'core_toolchain_source_sha256':core_sources,
  'checks':checks,'required_exports':required,'allowed_axioms':sorted(ALLOWED),
  'audited_declarations':len(names),'new_and_interface_inventory':len(inventory),'expression_nodes':len(nodes),
  'metadata_fallback_count':sum(r.get('encoding')=='native-repr' for r in decls),
  'artifact_sha256':artifacts,
  'inventory_scope':'All new construction module declarations and relevant native interfaces/constructors/projections; previously accepted prerequisite inventories retained by exact source bindings. All mathematical cylindrical modules audited by module origin, including private/generated declarations.',
  'expression_encoding':'Native JSON-lines Expr DAG with parsed per-node reconstruction and Expr.equal; metadata retained through explicitly tagged complete native Repr fallback. Types for all inventory declarations and bodies for computational definitions.',
  'remaining_scope':'Independent source-bound final review and exact private handoff; root combined integration/final acceptance/packaging are separate.'}
 (work/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 final=OUT/'construction';shutil.copytree(work,final,dirs_exist_ok=True)
 print(f'CYLINDRICAL_CONSTRUCTION_VERIFIED: {len(names)} allowed-only transitive audits, {len(inventory)} complete type inventories, {len(imports)} imported source bindings',flush=True)
if __name__=='__main__':main()
