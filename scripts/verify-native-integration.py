#!/usr/bin/env python3
"""Exact-source managed verification; isolated pinned dependencies reuse host caches."""
import gzip, hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/native-integration'
ALLOWED={'propext','Classical.choice','Quot.sound'}
PREFIX='ExactLiouvilleComparison.NativeIntegration'
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 os.chdir(ROOT)
 preserved=json.loads((OUT/'preservation.json').read_text())
 for p,e in preserved['files'].items(): assert digest(p)==e['sha256'],('Preserved source changed',p)
 inputs=set(Path('ExactLiouvilleComparison').glob('*.lean'))|{Path(p) for p in [
  'ExactLiouvilleComparison.lean','lean-toolchain','lakefile.toml','lake-manifest.json','.gitignore',
  'docs/objective.md','docs/reference/exact_liouville_comparison.tex','docs/native-integration-crosswalk.md',
  'scripts/verify-native-integration.py','verification/native-integration/Audit.lean',
  'verification/native-integration/preservation.json','verification/native-integration/accepted-receipts-revalidated.json',
  'verification/native-integration/receipt-agreement.json']}
 before={str(p):digest(p) for p in sorted(inputs)}
 scratch=Path(os.environ.get('NATIVE_INTEGRATION_CHECK_ROOT') or tempfile.mkdtemp(prefix='native-integration-source-',dir=os.environ.get('TMPDIR')))
 scratch.mkdir(exist_ok=True)
 for p in inputs:
  q=scratch/p;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 subprocess.run(['git','init','-q',str(scratch)],check=True)
 work=Path(tempfile.mkdtemp(prefix='native-integration-evidence-',dir=os.environ.get('TMPDIR')))
 print('Source:',scratch,'Evidence:',work,flush=True)
 env=dict(os.environ,NATIVE_INTEGRATION_AUDIT_DIR=str(work))
 checks=[]
 # Include four unchanged ancillary consumers bound by accepted receipts but omitted
 # from both deliveries. Their recovery is explicitly distinguished from remote inputs.
 targets=[PREFIX,'ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAudit']+[
  'ExactLiouvilleComparison.'+n for n in ['SteinRadialChecks','SteinReferenceConsumers',
  'SteinReferenceMetricChecks','SteinReferencePrimitiveConsumers']]
 for label,args,marker in [
  ('build',targets,None),
  ('audit',['--lean','verification/native-integration/Audit.lean'],'NATIVE_INTEGRATION_AUDIT_COMPLETE'),
  ('consumers',['--lean','ExactLiouvilleComparison/NativeIntegration.lean'],'NATIVE_INTEGRATION_CONSUMERS_COMPLETE')]:
  cmd=['horizon-lean-check','--root',str(scratch),*args]
  with (work/(label+'.log')).open('w') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
  log=(work/(label+'.log')).read_text()
  if r.returncode:print(log);raise SystemExit(r.returncode)
  receipt=json.loads([l for l in log.splitlines() if l.startswith('{')][-1])
  assert receipt['ok'] and receipt['snapshot_verified'],receipt
  if marker:assert marker in log.splitlines(),marker
  checks.append({'command':cmd,'managed':receipt});print(label+': passed',flush=True)
 assert len({c['managed']['source_key'] for c in checks})==1
 manifest=json.loads(Path('lake-manifest.json').read_text());pins={p['name']:p['rev'] for p in manifest['packages']}
 assert pins['mathlib']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
 assert pins['fsfltz']=='1a3d387cfacc746e25aad31e5b27b1803103e7cb'
 for pkg in manifest['packages']:
  p=scratch/'.lake/packages'/pkg['name']
  assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==pkg['rev']
  assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain'])
 # Revalidate the full union of both accepted component receipt source closures.
 accepted=json.loads((OUT/'accepted-receipts-revalidated.json').read_text())['sources']
 for p,h in accepted.items():
  q=scratch/p if p.startswith('.lake/') else ROOT/p
  assert digest(q)==h,('Accepted closure drift',p)
 names=(work/'names.txt').read_text().splitlines();inventory=(work/'inventory.txt').read_text().splitlines()
 assert len(names)==len(set(names)) and set(inventory)<=set(names)
 required=[PREFIX+'.'+n for n in ['constructedComparison','prescribedExtension','manuscript','complete',
  'allDimensions','everyPrescribedEnd','ConstructedComparison','PrescribedExtension']]+[
  'ExactLiouvilleComparison.'+n for n in ['FiniteTypePresentation.fromNative',
  'FiniteTypePresentation.QuotientData.comparisonFor','CylindricalCompatibility.existenceTarget',
  'CylindricalCompatibility.extensionTarget','CylindricalCompatibility.extension_of_prescribed_kernel',
  'ManuscriptComparison.manuscriptTarget','ManuscriptComparison.completeLiouvilleComparisonTarget']]
 assert set(required)<=set(inventory)
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
 sources=dict(before);imports=[];core_sources={}
 version=Path('lean-toolchain').read_text().strip().split(':v')[-1]
 core_root=Path('/opt/lean')/('lean-'+version+'-linux')/'src/lean'
 roots=[scratch]+[scratch/'.lake/packages'/p['name'] for p in manifest['packages']]
 for name in (work/'modules.txt').read_text().splitlines():
  rel=Path(name.replace('.','/')+'.lean');candidates=[r/rel for r in roots if (r/rel).is_file()]
  if not candidates:
   assert name.split('.')[0] in {'Init','Lean','Std','Lake'},name
   core=(core_root/'lake'/rel) if name.startswith('Lake.') else core_root/rel
   assert core.is_file(),core
   core_sources[str(core)]=digest(core);continue
  assert len(candidates)==1,(name,candidates)
  p=str(candidates[0].relative_to(scratch));sources[p]=digest(candidates[0]);imports.append({'module':name,'path':p,'sha256':sources[p]})
 assert before=={p:digest(p) for p in before},'Workspace source drift'
 assert before=={p:digest(scratch/p) for p in before},'Checked-copy drift'
 (work/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
 artifacts={str(p.relative_to(work)):digest(p) for p in work.rglob('*') if p.is_file()}
 result={'mission':'27db12fe-bb36-4bbe-b5c8-8c46236e3da2','mission_revision':1,
  'scope':'Native quotient then constructed cylindrical J then original comparison, full prescribed extension, manuscript and complete specialization',
  'inputs':preserved['inputs'],'source_sha256':sources,'imports':imports,
  'core_toolchain_source_sha256':core_sources,'pins':pins,'toolchain':Path('lean-toolchain').read_text().strip(),
  'checks':checks,'required_exports':required,'allowed_axioms':sorted(ALLOWED),
  'audited_declarations':len(names),'definition_assumption_inventory':len(inventory),'expression_nodes':len(nodes),
  'metadata_fallback_count':sum(r.get('encoding')=='native-repr' for r in decls),
  'artifact_sha256':artifacts,'accepted_receipt_bindings_revalidated':len(accepted),
  'inventory_scope':'All new module declarations plus stated interfaces, recursive project/FsFltz type and computational-definition closure, constructors and projections. Imported Mathlib/core reference boundary is enumerated and full imported sources hashed. Proof terms are checked by Lean and transitive axioms audited; existing source-bound component inventories/reviews are reused.',
  'expression_encoding':'Native JSON-lines Expr DAG, per-node parsed reconstruction and Expr.equal; complete tagged native Repr for metadata.',
  'remaining_scope':'Private publication/readback and final narrow review; root retains combined acceptance, host registration recovery and release.'}
 (work/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 shutil.copytree(work,OUT/'final',dirs_exist_ok=True)
 print(f'NATIVE_INTEGRATION_VERIFIED: {len(names)} transitive audits, {len(inventory)} type/definition closure declarations, {len(imports)} imported source bindings',flush=True)
if __name__=='__main__':main()
