#!/usr/bin/env python3
"""Source-selective import from exact private deliveries; never overwrite a mismatch."""
import base64, hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO = '31e09b7d-6080-4383-8e4e-92b14780690a'
OUT = ROOT/'verification/corollaries'
OUT.mkdir(parents=True, exist_ok=True)
manifest = []
seen = set()
def fetch(commit, path):
    key = (commit, path)
    if key in seen: return
    seen.add(key)
    url = f'/api/v3/repositories/{REPO}/file?commit_oid={commit}&path={path}'
    record = json.loads(subprocess.check_output(['horizon-pipeline','agent','request','GET',url]))
    assert record['commit_oid'] == commit and record['path'] == path
    data = base64.b64decode(record['content_base64'])
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == record['blob_oid']
    p = ROOT/path
    if p.exists(): assert p.read_bytes() == data, ('Existing source differs', path, commit)
    else:
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
    manifest.append(dict(commit=commit,path=path,blob_oid=record['blob_oid'],sha256=hashlib.sha256(data).hexdigest()))
    if path.endswith('.lean'):
        for dep in re.findall(r'^import (ExactLiouvilleComparison(?:\.[A-Za-z0-9_]+)+)',data.decode(),re.M):
            fetch(commit, dep.replace('.','/')+'.lean')
for commit, paths in [
 ('55493c9ba47cc09071f6abf0b16b901a95f19b1f', ['ExactLiouvilleComparison/MainComparison.lean','docs/main-comparison-proof.md']),
 ('4bb4bc2159d635b157f39a7d415cf2e63d491d4e', ['ExactLiouvilleComparison/SteinReference.lean']),
 ('f02720d55df5ea4ae0e16058f3614d090e0d832e', ['ExactLiouvilleComparison/SteinRadial.lean']),
 ('23046e70e5d55e308ec8d16a8a7aaaf7dd14c18b', ['ExactLiouvilleComparison/SteinGrowthConsumers.lean','docs/stein-growth-delivery.md']),
]:
    for path in paths: fetch(commit,path)
(OUT/'import-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Verified {len(manifest)} exact source bindings; preserved every existing file.')
