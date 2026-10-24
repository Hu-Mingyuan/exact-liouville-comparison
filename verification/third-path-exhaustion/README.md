# Third-path square-root scalar prerequisite

Mission `4c628a59-74bc-4f35-b15d-e0cadf9c4142`, revision 1. Parent assignment
`715bfb6e-da34-4a2a-b10b-1821801f6a8a` retains construction of the literal
third-path field, discharge of the helper premises, evolution, integration,
repair and final review. This packet proves only the assigned scalar prerequisite.
No mission correction or weakening was needed.

## Source and statement gate

The objective roadmap is `docs/sdu-continuation.md` at
`f8b5b6bcb56a18c0094d15fed4619ff100327e30`. The unchanged manuscript is
`docs/reference/exact_liouville_comparison.tex`. The accepted native
`RadialReference` and the literal `ThirdPath.exhaustion P x = sqrt(P.R x)`
are used directly. The delegated statement-review gate and source provenance are
recorded in the mission instructions: private source
`a7c3dcc18c4f4d695821fe619115c5b77c7988ed`, publication
`04df12f3-52ec-4061-9225-b3d1617e804e`.

The imported statement and crosswalk were copied without alteration from the
parent's read-only source. Their SHA-256 values were checked before proof:

- `ThirdPathStatement.lean`: `5cfd8cc26dadec7cf72da708c25d275b27d366ccf907a1e0d0d2c8977f2437ab`
- `docs/third-path-crosswalk.md`: `14737140da60ac599e25a199c7d46d3ca20b904d8a6eed4f604c1b15a0b78099`

`baseline.json` preserves all tracked Lean sources, pins and the manuscript from
that checkout, together with the reviewed statement and crosswalk hashes.

## Proof and reuse

Search order was pinned Mathlib, FsFltz, then the mandatory archived cluster
source; no new calculus, metric, manifold or ODE foundation was introduced.

1. Mathlib `Analysis/SpecialFunctions/Sqrt.lean` supplies
   `Real.contDiffAt_sqrt`, `Real.hasDerivAt_sqrt`, `Real.sqrt_le_sqrt` and
   `Real.sq_sqrt`. Since `P.lower_R` gives `R >= 1`, square root is smooth
   at every value of R. `ContDiffAt.comp_contMDiffAt` and
   `HasMFDerivAt.comp` give native manifold smoothness and the derivative.
   `Topology/Maps/Proper/Basic.lean` supplies `isProperMap_of_comp_of_t2`:
   squaring composed with the exhaustion equals the proper map R.
2. Pinned FsFltz `Geometry/Smooth.lean` defines `M.scalarDerivative f x v`
   literally as native `mfderiv` applied to v. The proof unfolds this actual
   definition for the chain-rule bridge, preserving the native tangent fiber.
3. The read-only archive `cluster-skeleton-2c239b0.tar.gz`, commit
   `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`, was inspected at
   `ClusterSkeleton/FiniteTimeConfinement.lean`. Its
   `norm_le_exp_abs_sub` / `abs_le_exp_abs_sub` concern actual curves with
   supplied derivative inequalities; `radial_component_bound` is specific
   to a seed's cluster field. They do not supply the arbitrary radial-reference
   square-root calculation or the reference-g norm estimate needed here.
4. Existing project bridges are reused:
   `CompatibleStructure.covector` transfers the same native linear functional
   to the explicit g-normed tangent space; its `le_opNorm` gives the dual bound.
   `MoserRegularity.NativeJoint.compact_scalar_bound` and `core_compact`
   supply uniform core control, including the empty-core case.

All eight new declarations are in `ExactLiouvilleComparison.ThirdPath` in the
single new semantic module `ThirdPathExhaustion.lean`:

| Declaration | Result |
| --- | --- |
| `exhaustion_smooth` | Native smoothness of the literal sqrt(R) |
| `exhaustion_lower` | Pointwise lower bound 1 |
| `exhaustion_bddBelow` | Bounded-below range, for continuation consumers |
| `exhaustion_proper` | Actual `IsProperMap` |
| `exhaustion_derivative` | Native derivative equals `(1/(2 sqrt(R))) dR(v)` |
| `exhaustion_exterior_bound` | At R > rstar, every vector of g norm at most 1 has absolute derivative at most `1/(2 sqrt(c))` |
| `exhaustion_core_bound` | Uniform interval/core bound for every native jointly regular field |
| `exhaustion_global_bound` | Uniform global bound under native joint regularity and the explicit g norm premise |

The exterior proof calls `radial_bound` only with `P.rstar < P.R x`.
It bounds `sqrt(c) * |dR|_(g dual)` by `sqrt(R)` without dividing by
`dR`, and so includes critical points and zero vectors. Every vector norm
premise explicitly uses `P.compatible.MetricTangent x`. Compactness supplies
core control independently of the radial identity or inequality. The global
constant is the maximum of the nonnegative core constant and the exterior
constant. There is no metric or primitive completeness premise and no flow claim.

## Reproduction and evidence

Run `python3 scripts/verify-third-path-exhaustion.py` with the installed pinned
caches and managed-check environment. It serially checks the library, generated
elaborated type inventory, transitive axiom audit, and the interval-field
consumer. Logs stay under TMPDIR during checks and are copied here afterward.
`receipt.json` records exact source hashes, pinned revisions, managed source
fingerprints and snapshot verification. `elaborated-types.txt` contains all
eight actual elaborated types; `declarations.json` inventories them.
The audit rejects any transitive axiom outside `propext`, `Classical.choice`,
and `Quot.sound`.

`Consumer.lean` checks precisely the scalar output types required by the parent
contract for an arbitrary interval vector field with its two explicit helper
premises. It neither assumes nor constructs the parent's Moser evolution.
The parent must discharge those premises for its literal field and retain final
integration review. This delivery does not establish the full comparison theorem.
