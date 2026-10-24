#!/usr/bin/env python3
"""Verify radial flow applicability only; the generic evolution remains a prerequisite."""
import hashlib,json,os,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT=Path('verification/radial-interpolation-flow')
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=json.loads((OUT/'inputs.json').read_text())
for p,h in base['files'].items(): assert digest(p)==h,('Changed input',p)
mods=[Path('ExactLiouvilleComparison')/(n+'.lean') for n in
 ['RadialInterpolationFlowStatement','ODETwoBarrierStatement','RadialInterpolationFlowInputs',
  'RadialInterpolationFlowCoefficients','RadialInterpolationFlowEqual']]
decls=[]
for p in mods:
 s=p.read_text(); ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 assert not re.search(r'\b(sorry|sorryAx|admit|axiom)\b',s),p
 decls += [{'file':str(p),'kind':k,'name':ns+'.'+n} for k,n in re.findall(r'^(def|theorem|structure) ([^\s({]+)',s,re.M)]
names=[x['name'] for x in decls]
(OUT/'input-declarations.json').write_text(json.dumps(decls,indent=2)+'\n')
for label,cmd in [('InputTypes','#check'),('InputAxiomAudit','#print axioms')]:
 (OUT/(label+'.lean')).write_text('import ExactLiouvilleComparison.RadialInterpolationFlowCoefficients\nimport ExactLiouvilleComparison.RadialInterpolationFlowEqual\n'+
  '\n'.join(cmd+' '+n for n in names)+'\n#eval IO.println "RADIAL_FLOW_'+label.upper()+'_COMPLETE"\n')
manifest=json.loads(Path('lake-manifest.json').read_text()); pins={p['name']:p['rev'] for p in manifest['packages']}
assert pins['mathlib']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz']=='1a3d387cfacc746e25aad31e5b27b1803103e7cb'
for pkg in ['mathlib','fsfltz']:
 assert subprocess.check_output(['git','-C','.lake/packages/'+pkg,'rev-parse','HEAD'],text=True).strip()==pins[pkg]
assert Path('lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.1'
sources=sorted(set([Path(p) for p in base['files']]+mods+
 [Path('scripts/verify-radial-interpolation-flow-inputs.py'),Path('docs/radial-interpolation-flow.md'),
 Path('.github/workflows/radial-interpolation-flow-inputs.yml'),OUT/'inputs.json',OUT/'input-declarations.json']+
 list(OUT.glob('*.lean'))+list(OUT.glob('*.md'))))
before={str(p):digest(p) for p in sources}
checks=[];managed=bool(os.environ.get('HORIZON_LEAN_BUILD'))
for label,args,marker in [
 ('inputs-build',['ExactLiouvilleComparison.RadialInterpolationFlowCoefficients'],None),
 ('equal-build',['ExactLiouvilleComparison.RadialInterpolationFlowEqual'],None),
 ('input-types',['--lean',str(OUT/'InputTypes.lean')],'RADIAL_FLOW_INPUTTYPES_COMPLETE'),
 ('input-axioms',['--lean',str(OUT/'InputAxiomAudit.lean')],'RADIAL_FLOW_INPUTAXIOMAUDIT_COMPLETE')]:
 cmd=(['horizon-lean-check']+args if managed else ['lake','env','lean',args[1]] if args[0]=='--lean' else ['lake','build']+args)
 r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (OUT/(label+'.log')).write_text(r.stdout)
 if r.returncode: print(r.stdout);raise SystemExit(r.returncode)
 assert '\ufffd' not in r.stdout,('Replacement character in evidence',label)
 record={'command':cmd,'returncode':r.returncode}
 if managed:
  record['managed']=json.loads([s for s in r.stdout.splitlines() if s.startswith('{')][-1])
  assert record['managed']['ok'] and record['managed']['snapshot_verified']
 if marker: assert marker in r.stdout.splitlines(),('Missing completion marker',label)
 if label=='input-types':
  for n in names: assert re.search(r'^'+re.escape(n)+r'(?:\s|[.{:])',r.stdout,re.M),n
 if label=='input-axioms':
  reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r.stdout)
  reports += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",r.stdout)]
  assert sorted(n for n,_ in reports)==sorted(names)
  record['declarations']={}
  for n,a in reports:
   ax=set(filter(None,re.split(r'[,\s]+',a)));assert ax<=ALLOWED,(n,ax)
   record['declarations'][n]=sorted(ax)
 checks.append(record)
assert before=={str(p):digest(p) for p in sources},'Source changed during check'
if managed:assert len({c['managed']['source_key'] for c in checks})==1
(OUT/'input-receipt.json').write_text(json.dumps({'scope':'Radial flow native applicability, k/A and 1/A coefficient applicability, conditional generic adapter, actual equal-coefficient Evolution and exterior critical-field zero. General two-barrier evolution NOT proved.',
 'statement_gate_commit':'70cb5f533db3755922378f2324a928398ac4b3a2',
 'source_sha256':before,'pins':pins,'checks':checks,'declaration_count':len(names),
 'allowed_axioms':sorted(ALLOWED),'remaining_prerequisite_mission':'c88064ba-ac8f-4ffe-b3aa-85315df3b9bf'},indent=2)+'\n')
print('Verified',len(names),'declarations; general flow remains open.')
