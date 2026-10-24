#!/usr/bin/env python3
"""Reproduce the bounded finite-type radial proof, full type inventory and axiom audit."""
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/finite-type-radial'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MODULES = ['FiniteTypeRadialStatement', 'FiniteTypeRadialRadius', 'FiniteTypeRadialGrowth',
    'FiniteTypeRadialMetricStatement', 'FiniteTypeRadialMetric', 'FiniteTypeRadialMetricChecks',
    'FiniteTypeRadial', 'FiniteTypeRadialConsumers']
PINS = {'mathlib': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
        'fsfltz': '1a3d387cfacc746e25aad31e5b27b1803103e7cb'}
DEPENDENCY_FILES = [
    '.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean',
    '.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean',
    '.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean',
    '.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Group.lean',
    '.lake/packages/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean',
    '.lake/packages/mathlib/Mathlib/Topology/Maps/Proper/CompactlyGenerated.lean',
    '.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/ExteriorDerivative.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/FixedAmbient.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/Liouville.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/CompletionCollar.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/CompletionCollarExtension.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/CompletionIntervalMapFamily.lean',
    '.lake/packages/fsfltz/FsFltz/Geometry/BoundarySmooth.lean',
]


def digest(path):
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def main():
    baseline = json.loads((OUT / 'baseline.json').read_text())
    for path, expected in baseline['files'].items():
        assert digest(path) == expected, ('Changed preserved source', path)
    # Snapshot-only files belonged to prior work and are not needed by this delivery.
    for path, expected in baseline.get('workspace_only_files', {}).items():
        if (ROOT / path).exists():
            assert digest(path) == expected, ('Changed unrelated workspace source', path)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    pins = {p['name']: p['rev'] for p in manifest['packages']}
    for dep, pin in PINS.items():
        assert pins[dep] == pin
        actual = subprocess.check_output(['git', '-C', str(ROOT / '.lake/packages' / dep),
            'rev-parse', 'HEAD'], text=True).strip()
        assert actual == pin, (dep, actual)
        subprocess.run(['git', '-C', str(ROOT / '.lake/packages' / dep),
            'diff', '--exit-code', 'HEAD', '--', '*.lean'], check=True, capture_output=True)
    child = json.loads((ROOT / 'verification/finite-type-radial-metric/receipt.json').read_text())
    for path, expected in child['source_sha256'].items():
        assert digest(path) == expected, ('Changed delivered child source', path)
    child_dependencies = {'.lake/packages/' + p: h for p, h in child['dependency_sha256'].items()}
    for path, expected in child_dependencies.items():
        assert digest(path) == expected, ('Changed child dependency', path)
    declarations = []
    for module in MODULES:
        path = f'ExactLiouvilleComparison/{module}.lean'
        source = (ROOT / path).read_text()
        assert not re.search(r'\b(sorry|sorryAx|admit|axiom|unsafe|opaque)\b', source), path
        for kind, name in re.findall(r'^(def|theorem|structure) ([^\s({]+)', source, re.M):
            declarations.append({'file': path, 'kind': kind,
                'name': 'ExactLiouvilleComparison.' +
                    ('FiniteTypeRadialMetric.' if module.startswith('FiniteTypeRadialMetric')
                     else 'FiniteTypeRadial.') + name})
    expected_names = {d['name'] for d in declarations}
    assert len(expected_names) == len(declarations)
    paths = sorted(set(baseline['files']) | set(DEPENDENCY_FILES) |
        set(child['source_sha256']) | set(child_dependencies) |
        {d['file'] for d in declarations} | {
        'docs/finite-type-radial-crosswalk.md', 'docs/finite-type-radial-proof-guide.md',
        'verification/finite-type-radial-metric/receipt.json',
        'verification/finite-type-radial-metric/final-review.md',
        'scripts/verify-finite-type-radial.py', 'verification/finite-type-radial/Audit.lean',
        'verification/finite-type-radial/baseline.json', 'verification/finite-type-radial/statement-review.md',
        'verification/finite-type-radial/StatementInventory.lean'})
    before = {p: digest(p) for p in paths}
    scratch = Path(tempfile.mkdtemp(prefix='finite-type-radial-', dir=os.environ.get('TMPDIR')))
    checks, logs = [], {}
    managed = bool(os.environ.get('HORIZON_LEAN_BUILD'))
    for label, args in [
        ('build', ['ExactLiouvilleComparison.FiniteTypeRadialConsumers']),
        ('audit', ['--lean', 'verification/finite-type-radial/Audit.lean'])]:
        command = (['horizon-lean-check'] + args if managed else
                   ['lake', 'env', 'lean', args[1]] if args[0] == '--lean' else ['lake', 'build'] + args)
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
            env=dict(os.environ, FINITE_TYPE_RADIAL_AUDIT_OUTPUT=str(scratch / 'audit')))
        logs[label] = result.stderr + result.stdout
        (scratch / (label + '.log')).write_text(logs[label])
        if result.returncode:
            raise RuntimeError(logs[label])
        check = {'command': command, 'returncode': result.returncode}
        if managed:
            check['managed'] = json.loads(result.stdout)
            assert check['managed']['ok'] and check['managed']['snapshot_verified']
        checks.append(check)
    assert 'FINITE_TYPE_RADIAL_AUDIT_COMPLETE' in logs['audit'].splitlines()
    names = (scratch / 'audit.names').read_text().splitlines()
    assert expected_names <= set(names)
    types = (scratch / 'audit.types').read_text()
    assert '⋯' not in types, 'Elided expanded type inventory'
    readable = (scratch / 'audit.readable').read_text()
    assert '⋯' not in readable, 'Elided readable type inventory'
    audit = {}
    for line in (scratch / 'audit.axioms').read_text().splitlines():
        name, ax = line.split('\t')
        actual = set(filter(None, ax.split(',')))
        assert actual <= ALLOWED, (name, actual)
        assert name not in audit
        audit[name] = sorted(actual)
    assert set(audit) == set(names)
    for name in names:
        assert name + ' : ' in types, name
    for name in ['radius', 'radius_smooth', 'radius_proper', 'compact_farEnd_compl', 'growthWitnessTarget', 'constructedRadius', 'reference',
                 'constructionTarget', 'consumerTarget', 'checked_construction', 'checked_consumer',
                 'constructed_growth_witness']:
        assert 'ExactLiouvilleComparison.FiniteTypeRadial.' + name in audit
    assert before == {p: digest(p) for p in paths}
    if managed:
        assert len({c['managed']['source_key'] for c in checks}) == 1
    # No writes inside the checked workspace until both managed checks have completed.
    for label, log in logs.items():
        (OUT / ('final-' + label + '.txt')).write_text(log)
    (OUT / 'elaborated-types.txt').write_text(readable)
    (OUT / 'elaborated-types-full.txt.gz').write_bytes(gzip.compress(types.encode(), mtime=0))
    (OUT / 'declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    (OUT / 'environment-declarations.json').write_text(json.dumps(names, indent=2) + '\n')
    (OUT / 'axiom-audit.json').write_text(json.dumps(audit, indent=2) + '\n')
    (OUT / 'receipt.json').write_text(json.dumps({
        'scope': 'Complete bounded finite-type radius, original metric reference and unchanged-witness growth bridge; no comparison theorem',
        'metric_child_commit': '9716da2fdab7d268cfea6fbc3808a40cf3a47546',
        'input_commit': baseline['input_commit'], 'source_sha256': before,
        'pins': pins, 'checks': checks, 'allowed_axioms': sorted(ALLOWED),
        'expanded_types_sha256': hashlib.sha256(types.encode()).hexdigest(),
        'expanded_types_bytes': len(types.encode()),
        'source_declaration_count': len(declarations), 'environment_declaration_count': len(names),
        'excluded_root_owned': ['FiniteTypeTarget comparison',
            'MainTarget', 'exactness and comparison assembly', 'final packaging and acceptance']
    }, indent=2) + '\n')
    print(f'Verified {len(declarations)} source declarations and {len(names)} elaborated declarations; allowed-only transitive audit.')


if __name__ == '__main__':
    main()
