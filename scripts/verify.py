#!/usr/bin/env python3
"""Verify the publication interface; adapted from cluster-skeleton/scripts/verify.py.

The mathematical source must match the accepted library manifest. Ordinary use
requires Lake only. --managed uses an already configured Horizon host and caches.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/publication'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ENV = dict(os.environ)
ENV.setdefault('MATHLIB_NO_CACHE_ON_UPDATE', '1')
ENV.setdefault('LEAN_NUM_THREADS', '2')


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--managed', action='store_true')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    receipt = OUT / 'receipt.json'
    result = {'status': 'running', 'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'scope': 'accepted library equality, public entry point, consumers and final-root transitive axioms',
              'mode': 'managed' if args.managed else 'lake'}
    receipt.write_text(json.dumps(result, indent=2) + '\n')
    checks = []

    def run(command, label):
        print('Checking:', label, flush=True)
        path = OUT / (label + '.log')
        with path.open('w') as stream:
            proc = subprocess.run(command, cwd=ROOT, env=ENV, stdout=stream, stderr=subprocess.STDOUT)
        log = path.read_text()
        if proc.returncode:
            raise RuntimeError(f'{label} failed ({proc.returncode}): {log[-5000:]}')
        check = {'command': command, 'returncode': proc.returncode}
        if args.managed:
            managed = json.loads([line for line in log.splitlines() if line.startswith('{')][-1])
            if not managed.get('ok') or not managed.get('snapshot_verified'):
                raise RuntimeError(f'{label}: unverified managed snapshot')
            check['managed'] = managed
        checks.append(check)
        print('Passed:', label, flush=True)
        return log

    try:
        sources = sorted((ROOT / 'ExactLiouvilleComparison').rglob('*.lean'))
        hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in sources}
        accepted = json.loads((ROOT / 'verification/accepted-library.json').read_text())
        if hashes != accepted['source_sha256']:
            raise RuntimeError('Mathematical library differs from the independently accepted source')
        tracked = sources + [ROOT / p for p in ('ExactLiouvilleComparison.lean', 'lean-toolchain',
            'lakefile.toml', 'lake-manifest.json', 'verification/FinalConsumer.lean',
            'verification/PublicationAxioms.lean', 'verification/accepted-library.json', 'scripts/verify.py')]
        before = {p.relative_to(ROOT).as_posix(): digest(p) for p in tracked}
        if args.managed:
            prefix = ['horizon-lean-check', '--root', str(ROOT)]
            run(prefix + ['ExactLiouvilleComparison'], 'build')
            run(prefix + ['--lean', 'verification/FinalConsumer.lean'], 'consumer')
            log = run(prefix + ['--lean', 'verification/PublicationAxioms.lean'], 'axioms')
            if len({x['managed']['source_key'] for x in checks}) != 1:
                raise RuntimeError('Managed checks used different source snapshots')
        else:
            run(['lake', '--rehash', 'build', 'ExactLiouvilleComparison'], 'build')
            run(['lake', 'env', 'lean', 'verification/FinalConsumer.lean'], 'consumer')
            log = run(['lake', 'env', 'lean', 'verification/PublicationAxioms.lean'], 'axioms')
        version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, env=ENV, text=True).strip()
        if 'version 4.34.1,' not in version:
            raise RuntimeError('Unexpected Lean toolchain: ' + version)
        pins = {}
        for package in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']:
            dep = ROOT / '.lake/packages' / package['name']
            actual = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], env=ENV, text=True).strip()
            if package['type'] != 'git' or actual != package['rev']:
                raise RuntimeError('Unexpected dependency revision: ' + package['name'])
            if subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain'], env=ENV):
                raise RuntimeError('Modified dependency: ' + package['name'])
            pins[package['name']] = actual
        expected = set(re.findall(r'^#print axioms (\S+)', (ROOT / 'verification/PublicationAxioms.lean').read_text(), re.M))
        entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
        ax = {name: sorted({x.strip() for x in raw.split(',') if x.strip()}) for name, raw in entries}
        ax.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", log)})
        if set(ax) != expected:
            raise RuntimeError('Missing or unexpected audited declarations: ' + str(expected ^ set(ax)))
        for name, used in ax.items():
            if not set(used) <= ALLOWED:
                raise RuntimeError('Forbidden axiom in ' + name + ': ' + str(used))
        if before != {p.relative_to(ROOT).as_posix(): digest(p) for p in tracked}:
            raise RuntimeError('Source changed during verification')
        result.update(status='passed', checks=checks, lean_version=version, dependency_commits=pins,
            accepted_library_commit=accepted['accepted_commit'], accepted_library_files=len(hashes),
            source_sha256=before, allowed_axioms=sorted(ALLOWED), final_root_axioms=ax,
            evidence_sha256={p.name: digest(p) for p in OUT.glob('*.log')})
    except Exception as exc:
        result.update(status='failed', error=str(exc), checks=checks)
        raise
    finally:
        result['finished_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        receipt.write_text(json.dumps(result, indent=2) + '\n')
    print('PUBLICATION_INTERFACE_VERIFIED', flush=True)


if __name__ == '__main__':
    main()
