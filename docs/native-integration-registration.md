# Exact-source registration repair

This is registration diagnosis, not a ready-workspace or phase-acceptance claim.
The final delivery record supplies the exact integrated private commit and branch.

The API workspace readback is retained in
`verification/native-integration/workspace-records.json`. All seven returned
records identify `f8b5b6bcb56a18c0094d15fed4619ff100327e30`; none identifies the
accepted cylindrical/adapter union. In particular the current workspace is
`6c6d0122-6ab8-58e7-ab33-960741f8d4bd` r2 at
`/var/lib/archon-worker/workspaces/assignments/57837227-ce81-4390-a06d-88075fd4d5e7`.
Its Git HEAD is the old commit and the later accepted sources are untracked.
Its protected Git metadata is not rewritten. Merely patching head metadata to
the integrated commit would misrepresent this checkout.

The initial managed check additionally found unusable inherited dependency
links: Git ownership blocked inspection of fsfltz and the mathlib symlink
resolved to a directory without its own Git checkout. We preserved those paths
and used a fresh isolated scratch source, with managed checkout preparation from
the existing local pinned Git/artifact caches. Its dependency revisions,
cleanliness and actual imported source hashes are checked. No upstream source,
dependency pin, shared cache or old project was edited. The scratch build is
verification evidence; it is not a registered workspace or a published Git HEAD.

## Remaining owner and action

Integration/recovery owner: root mission
`91f6a7c7-1eb9-4e2c-bb7e-39389d62ea18`, through its existing scheduler successor
`b635300f-f340-435c-a3d2-0e9bd94090c7`. Physical checkout/verification owner: the
operator of enrolled host `22403293-2d3a-4b88-8890-35a057a61932`.
No new planner, proof author or duplicate repair session is requested.

1. Use the final verified publication's exact branch and commit to create a
   separate clean checkout in that host's configured workspace roots. Preserve
   existing dirty workspaces. The checkout must contain the actual Git commit,
   both components and the integration consumer, with matching branch and clean
   status. Prepare pinned dependencies using the existing managed caches.
2. The root-authorized maintainer registers that real checkout through
   `POST /api/v3/records/workspace`, with project
   `6e03a624-b2d1-4daa-a9e0-da83d9e8f2e3`, repository
   `31e09b7d-6080-4383-8e4e-92b14780690a`, the host above, actual path/branch,
   exact final commit as base/head and `status: preparing`.
3. The authenticated host/operator runs supported `horizon-pipeline
   verify-workspaces --worker-config <existing worker config> --operator
   <operator>`, then its `--apply` only after successful inspection. Installed
   `execution/workspace_setup.py:inspect_checkout` checks actual Git root,
   branch, base ancestry, HEAD and clean status; `verify` requires installation
   admin and that enrolled host credential. No agent borrows those credentials.
4. Read back the resulting workspace ID, revision, ready status and exact head;
   attach it to root's acceptance evidence before any phase transition.

Installed `projects/catalog.py` requires maintainer authority for workspace
creation/update; this mission is a worker. Host details GET returned 403
`Installation administrator permission is required`. There is no worker
`register_workspace` lifecycle command. These are concrete authority/source
constraints, not a request for broader proof work. This mission delivers the
permitted alternative: exact verified source readiness plus a precisely owned
registration repair. Root alone decides combined acceptance, recovery and later
release. No stale metadata is relabeled, no phase transition or GitHub upload
is performed.
