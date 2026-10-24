#!/usr/bin/env python3
"""Serial build, declaration inventory and transitive audit of the full ODE target."""
import hashlib
import json
import os
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
V = ROOT / 'verification/ode-two-barrier'
os.chdir(ROOT)
binding = json.loads((V / 'source-binding.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
def digest(rel):
    return hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
for rel, expected in {**binding['baseline_files_sha256'], **binding['new_lean_sha256']}.items():
    assert digest(rel) == expected, rel
pins = {p['name']: p['rev'] for p in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']}
for pkg in ['mathlib', 'fsfltz']:
    assert pins[pkg] == binding['pins'][pkg]
    directory = ROOT / '.lake/packages' / pkg
    assert subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip() == pins[pkg]
    assert not subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain'], text=True).strip()
assert (ROOT / 'lean-toolchain').read_text().strip() == binding['pins']['lean']
decls = []
for rel in binding['new_lean_sha256']:
    content = (ROOT / rel).read_text()
    assert not re.search(r'\b(sorry|sorryAx|admit|axiom)\b', content), rel
    namespaces = []
    for line in content.splitlines():
        if m := re.match(r'namespace (\S+)', line):
            namespaces.append(m[1])
        elif re.match(r'end(?: |$)', line):
            if namespaces:
                namespaces.pop()
        elif m := re.match(r'(def|structure|theorem) ([^\s({]+)', line):
            decls.append({'file': rel, 'kind': m[1], 'name': '.'.join(namespaces + [m[2]])})
names = [d['name'] for d in decls]
assert len(names) == len(set(names)) == 28
(V / 'declarations.json').write_text(json.dumps(decls, indent=2) + '\n')
for file, command in [('DeclarationTypes', '#check'), ('AxiomAudit', '#print axioms')]:
    text = 'import ExactLiouvilleComparison.ODETwoBarrier\n\n'
    text += '\n'.join(command + ' ' + name for name in names) + '\n'
    if file == 'DeclarationTypes':
        text += '#print ExactLiouvilleComparison.ODE.TwoBarrierEvolutionTarget\n'
        text += '#print ExactLiouvilleComparison.FirstPathFlow.Evolution\n'
        text += '#print ExactLiouvilleComparison.ODE.twoBarrierEvolution\n'
    text += '#eval IO.println "TWO_BARRIER_' + file.upper() + '_COMPLETE"\n'
    (V / (file + '.lean')).write_text(text)
sources = sorted(set(binding['baseline_files_sha256']) | set(binding['new_lean_sha256']) |
                 {'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'docs/ode-two-barrier.md',
                  'scripts/verify-ode-two-barrier.py', '.github/workflows/ode-two-barrier.yml'} |
                 {str(p.relative_to(ROOT)) for p in V.iterdir() if p.suffix in {'.lean', '.md'}} |
                 {'verification/ode-two-barrier/source-binding.json',
                  'verification/ode-two-barrier/declarations.json'})
before = {rel: digest(rel) for rel in sources}
managed = bool(os.environ.get('HORIZON_LEAN_BUILD'))
checks, logs = [], {}
for label, args, marker in [
    ('build', ['ExactLiouvilleComparison.ODETwoBarrier'], None),
    ('types', ['--lean', 'verification/ode-two-barrier/DeclarationTypes.lean'], 'TWO_BARRIER_DECLARATIONTYPES_COMPLETE'),
    ('axioms', ['--lean', 'verification/ode-two-barrier/AxiomAudit.lean'], 'TWO_BARRIER_AXIOMAUDIT_COMPLETE')]:
    if managed:
        command = ['horizon-lean-check', '--root', str(ROOT), *args]
    elif args[0] == '--lean':
        command = ['lake', 'env', 'lean', args[1]]
    else:
        command = ['lake', 'build', *args]
    p = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logs[label] = p.stdout
    if p.returncode:
        print(p.stdout)
        raise SystemExit(p.returncode)
    record = {'command': command, 'returncode': p.returncode}
    if managed:
        receipt = json.loads(p.stdout.splitlines()[-1])
        assert receipt['ok'] and receipt['snapshot_verified'], receipt
        record['managed'] = receipt
    if marker:
        assert marker in p.stdout.splitlines(), (label, 'missing completion marker')
    if label == 'types':
        for name in names:
            assert re.search(r'^' + re.escape(name) + r'(?:\s|[.{:])', p.stdout, re.M), name
    if label == 'axioms':
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", p.stdout)
        reports += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", p.stdout)]
        assert sorted(n for n, _ in reports) == sorted(names)
        record['declarations'] = {}
        for name, axioms in reports:
            used = set(filter(None, re.split(r'[,\s]+', axioms)))
            assert used <= allowed, (name, used)
            record['declarations'][name] = sorted(used)
    checks.append(record)
assert before == {rel: digest(rel) for rel in sources}, 'Source changed during verification'
if managed:
    assert len({c['managed']['source_key'] for c in checks}) == 1
# Write receipts only after all checks, so managed fingerprints bind one stable source.
for label, text in logs.items():
    (V / (label + '.log')).write_text(text)
(V / 'receipt.json').write_text(json.dumps({
    'scope': 'Full unchanged ODE.TwoBarrierEvolutionTarget, generic ODE infrastructure only',
    'baseline_commit': binding['base_commit'], 'source_sha256': before,
    'pins': pins, 'checks': checks, 'explicit_declaration_count': len(names),
    'allowed_axioms': sorted(allowed)}, indent=2) + '\n')
print('Verified full TwoBarrierEvolutionTarget:', len(names), 'declarations; allowed-only transitive axioms.')
