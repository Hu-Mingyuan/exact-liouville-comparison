# Third-path definition crosswalk

Scope: mission `4cc7ff50-61b6-4e8c-adc1-29bb17a21549`, revision 1.
Baseline: `f8b5b6bcb56a18c0094d15fed4619ff100327e30`, with mathematical base
`9306b794082d1acb905f8fec4d2dfae3db37b88f`. The versioned objective is roadmap
document `86760810-08b9-4687-a4a9-37f6a45e361c`, revision 1, whose source is
`docs/sdu-continuation.md` at the baseline. Historical API identifiers in that
file are provenance only.

The new bounded specification is `ExactLiouvilleComparison.ThirdPath.Target`
in `ExactLiouvilleComparison/ThirdPathStatement.lean`. It is a proposition to
prove, not a proof. `Construction` is exclusively output data. No caller supplies
its field, trajectories, regularity, estimates or evolution.

| Manuscript object | Literal declaration and meaning |
| --- | --- |
| Arbitrary finite-dimensional manifold without boundary | Pinned FsFltz `SmoothManifold d`, bundling native Mathlib `ChartedSpace`, `IsManifold`, Hausdorff and second-countability data; tangent is native `TangentSpace` |
| Smooth forms and d | `M.Form k` is a continuous alternating map on native tangent fibers; `M.IsSmoothForm` uses actual inverse-chart derivatives; `M.exteriorDerivative` transports Mathlib `extDeriv` of chart coefficients |
| Reference beta, J, g, R | Unchanged `RadialReference M`; `CompatibleStructure.g` is a native smooth Riemannian metric and `metric_eq` identifies it with d beta(.,J.) |
| Compact-core exception | Only `{R > rstar}` carries `radial_identity` and the radial dual-norm inequality; `R >= 1` and native properness make `{R <= rstar}` compact |
| lambda and weak taming | `ExactSymplecticStructure M` supplies the actual smooth primitive and symplectic differential; `WeaklyTames` is nonnegative, not positive, on `(v,Jv)` |
| Literal A | Unchanged `LargeCoefficient.A P T.primitive`, the locally finite smooth-transition series using compact-sublevel suprema; no freely chosen dominating function |
| Forward path | `ThirdPath.primitive P T s = A(R) beta + s lambda`, for real s; symplecticity is required only for `s : Parameter = [0,1]` |
| Moser sign | `Construction.equation`: d mu_s(X_s,v) = -lambda(v), using positive contraction in the first slot; `unique_field` quantifies every native tangent vector |
| Tangent and dual norms | `P.compatible.MetricTangent x` and `P.compatible.dualNorm x (oneCovector T.primitive x)` use g, not the default chart norm |
| Scalar continuation function | `ThirdPath.exhaustion P = sqrt(R)`; output requires smoothness, actual `IsProperMap`, lower bound 1, exterior estimate, core bound and global absolute derivative bound |
| Endpoint regularity | `MoserRegularity.NativeJoint` has one extension smooth at every point of the closed spacetime strip; no fixed negative-time strip or off-interval symplecticity hypothesis |
| Actual full evolution | Unchanged `FirstPathFlow.Evolution`: native `Diffeomorph`s for every initial/terminal pair, an extension jointly smooth on an open neighborhood, within-ODEs at endpoints, chart ODEs, closed-interval uniqueness, composition and inverse identities |
| Identity-start and inverse endpoint | Evolution supplies the forward isotopy. Additional `inverse_isotopy` refers literally to `map parameterOne parameterZero`; `Evolution.inverse` identifies it with the inverse of `map parameterZero parameterOne` |

The inverse endpoint is the map used for the manuscript arrow
`lambda + A beta -> A beta`. Pullback exactness, its primitive integral, and
four-stage assembly remain root-owned. This statement does not claim them.

The third path does not use B or the inverse-form growth bound. Omitting those
unused hypotheses strengthens this intermediate lemma and leaves the complete
comparison theorem unchanged. It adds no completeness assumption on g, beta or
lambda and no upper growth restriction on lambda or A. No object newly named a
Liouville manifold is introduced; the preserved complete-Liouville definitions
still require actual all-real-time flows.

## Reuse and proof route

Search order is pinned Mathlib, pinned FsFltz, then the archived cluster source.
Mathlib `Dynamics/Flow.lean` defines an autonomous continuous additive action;
it does not itself specify this nonautonomous two-time evolution. Mathlib
`Geometry/Manifold/IntegralCurve/ExistUnique.lean` and `Analysis/ODE/ExistUnique.lean`
provide local existence infrastructure. The delivered project already bridges
these capabilities to the stronger needed bounded evolution, so no replacement
ODE foundation is planned.

The mandatory third search inspected archived cluster-skeleton commit
`2c239b0c03922a1549f18ee3a45a8e0ca25bb28c` from the read-only reference tarball.
`ClusterSkeleton/GeometryTarget.lean` defines `LiouvilleData` with the literal
FsFltz complete flow and its carrier-preserving conversion.
`ClusterSkeleton/NativeCompleteFlow.lean` constructs an all-real autonomous
flow for its particular cluster field via native integral curves and
`CollarFlow.contMDiff_joint_of_isMIntegralCurve`. It supplies neither the
third-path inverse field nor the required nonautonomous continuation theorem
on arbitrary radial geometry. The accepted generic ODE modules in this project
are the appropriate reuse layer; no cluster source is modified or imported.

Pinned FsFltz `Geometry/Smooth.lean` supplies the native wrappers listed above.
The project already proves inverse-contraction and regularity bridges:
`CompatibleStructure.inverseContraction_equation`,
`MoserRegularity.intervalSmooth_of_equation`,
`ODE.native_open_of_interval_family`, and
`FirstPathFlow.evolution_of_scalar_bound`. The latter's actual premises are
open-neighborhood native smoothness, a smooth proper bounded-below scalar, and
a uniform bound on its actual spatial derivative. These must all be proved.

The intended field is the inverse positive contraction of the literal d mu_s
applied to `-lambda`. Equality with any regularity helper's inverse must follow
from the field equation and nondegeneracy. The norm estimate comes from evaluating
that equation on JX, the radial metric lower bound A g, and the g-dual norm.
The exterior sqrt(R) estimate uses only the exterior radial inequality. Native
continuity on the compact parameter/core product supplies the missing core bound.

## Gate and remaining obligations

Compilation and independent source-bound statement review are required before
substantive proof work. The gate receipt will record exact source hashes and
review findings. Final delivery additionally needs constructed proof terms,
literal-A consumers, elaborated types, an allowed-only transitive axiom audit,
serial managed checks, and independent final review. The mission remains open
until those outcomes are delivered and accepted.
