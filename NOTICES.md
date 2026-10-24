# Source and dependency notices

The mathematical source is the user-supplied manuscript identified, with its unchanged source hash, in [docs/sources.json](docs/sources.json). This repository is public. This notice does not grant a new license for the manuscript or original project work.

The Lean library directly imports these pinned upstream dependencies. Their original source files and license terms are retained when Lake materializes them:

| Dependency | Revision | Upstream license |
| --- | --- | --- |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Apache License 2.0; see `.lake/packages/mathlib/LICENSE` |
| [Bohan Fang's FsFltz](https://github.com/bohanfang/fs-fltz-minimal) | `1a3d387cfacc746e25aad31e5b27b1803103e7cb` | Apache License 2.0; see `.lake/packages/fsfltz/LICENSE` |

All transitive package revisions are fixed by `lake-manifest.json`; their upstream license files remain in their dependency checkouts. Dependencies and compiled caches are not vendored into this repository.

The document layout, dependency-cache script, verification-driver structure, and CI workflow reuse the user's separate `Hu-Mingyuan/cluster-skeleton` project at `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`. That project has not been modified. The exact accepted mathematical library and source-bound independent reviews are described in [verification/README.md](verification/README.md).
