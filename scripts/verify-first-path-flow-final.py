#!/usr/bin/env python3
"""Verify the constructed first-path evolution, literal consumers and transitive axioms."""
import hashlib,json,os,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT=Path('verification/first-path-flow-final')
OUT.mkdir(exist_ok=True)
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=json.loads((OUT/'base-source.json').read_text())
for p,h in base['files'].items():
    assert digest(p)==h,('Changed input',p)
mods=[Path('ExactLiouvilleComparison')/(n+'.lean') for n in
 ['FirstPathFlowStatement','ODEContinuationStatement','ODEIntervalRegularity',
  'ODEScalarConfinement','FirstPathFlowInputs','FirstPathFlowChecks',
  'ODEContinuationCutoff','ODEContinuation','ODEGlobalField','ODEGlobalExistence',
  'ODESmoothEvolution','ODEClosedUniqueness','FirstPathFlow','FirstPathFlowFinalChecks']]
decls=[]
for p in mods:
    s=p.read_text(); ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
    assert not re.search(r'\b(sorry|sorryAx|admit|axiom)\b',s),p
    decls += [{'file':str(p),'kind':k,'name':ns+'.'+n} for k,n in
      re.findall(r'^(def|structure|theorem) ([^\s({]+)',s,re.M)]
names=[x['name'] for x in decls]
(OUT/'declarations.json').write_text(json.dumps(decls,indent=2)+'\n')
for name,cmd in [('Types','#check'),('AxiomAudit','#print axioms')]:
    (OUT/(name+'.lean')).write_text('import ExactLiouvilleComparison.FirstPathFlowFinalChecks\n'+
      '\n'.join(cmd+' '+n for n in names)+'\n#eval IO.println "FIRST_PATH_FLOW_FINAL_'+name.upper()+'_COMPLETE"\n')
manifest=json.loads(Path('lake-manifest.json').read_text()); pins={p['name']:p['rev'] for p in manifest['packages']}
assert pins['mathlib']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
assert pins['fsfltz']=='1a3d387cfacc746e25aad31e5b27b1803103e7cb'
for pkg in ['mathlib','fsfltz']:
    assert subprocess.check_output(['git','-C','.lake/packages/'+pkg,'rev-parse','HEAD'],text=True).strip()==pins[pkg]
assert Path('lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.1'
sources=sorted(set([Path(p) for p in base['files']]+mods+[Path('scripts/verify-first-path-flow-final.py'),Path('docs/first-path-flow-final.md'),
    Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain'),
    Path('.github/workflows/first-path-flow.yml')]+
    list(OUT.glob('*.lean'))+list(OUT.glob('*.md'))+[OUT/'base-source.json',OUT/'declarations.json']))
before={str(p):digest(p) for p in sources}
checks=[]
for label,args,marker in [
 ('build',['ExactLiouvilleComparison.FirstPathFlowFinalChecks'],None),
 ('types',['--lean',str(OUT/'Types.lean')],'FIRST_PATH_FLOW_FINAL_TYPES_COMPLETE'),
 ('axioms',['--lean',str(OUT/'AxiomAudit.lean')],'FIRST_PATH_FLOW_FINAL_AXIOMAUDIT_COMPLETE')]:
    managed=bool(os.environ.get('HORIZON_LEAN_BUILD'))
    cmd=(['horizon-lean-check']+args if managed else
      ['lake','env','lean',args[1]] if args[0]=='--lean' else ['lake','build']+args)
    r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (OUT/(label+'.log')).write_text(r.stdout)
    if r.returncode: print(r.stdout); raise SystemExit(r.returncode)
    record={'command':cmd,'returncode':r.returncode}
    if managed:
      record['managed']=json.loads([s for s in r.stdout.splitlines() if s.startswith('{')][-1])
      assert record['managed']['ok'] and record['managed']['snapshot_verified']
    if marker: assert marker in r.stdout.splitlines(),('Missing output',label)
    if label=='types':
      for n in names: assert re.search(r'^'+re.escape(n)+r'(?:\s|[.{:])',r.stdout,re.M),n
    if label=='axioms':
      reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r.stdout)
      reports += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",r.stdout)]
      assert sorted(n for n,_ in reports)==sorted(names)
      record['declarations']={}
      for n,a in reports:
        ax=set(filter(None,re.split(r'[,\s]+',a)));assert ax<=ALLOWED,(n,ax)
        record['declarations'][n]=sorted(ax)
    checks.append(record)
assert before=={str(p):digest(p) for p in sources},'Source changed during check'
if managed: assert len({c['managed']['source_key'] for c in checks})==1
(OUT/'receipt.json').write_text(json.dumps({'scope':'Constructed first-path global smooth evolution of literal FirstPath.X: actual ODE, both directions, endpoints, closed uniqueness, smooth dependence, inverse/evolution identities and identity-start diffeomorphism isotopy. No comparison or exactness claim.',
 'base_commit':base['commit'],'source_sha256':before,'pins':pins,'checks':checks,
 'inherited_file_count':len(base['files']),'declaration_count':len(names),'allowed_axioms':sorted(ALLOWED)},indent=2)+'\n')
print('Verified',len(names),'declarations; first-path evolution construction and original growth consumer audited.')
