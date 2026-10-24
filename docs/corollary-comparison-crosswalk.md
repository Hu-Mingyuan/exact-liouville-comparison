# Stein and common-reference application crosswalk

Mission b518dc8e-9cf8-40a0-b7dd-1199bf9c17a3 revision 1. This gate concerns
manuscript `cor:stein`, `eq:steinsetup`, `eq:steinradial`, and `cor:two`.
`CorollaryComparisonStatement.lean` aliases the three unchanged targets and
specifies the constructed reference and explicit common-reference witnesses.
These specifications are not proofs. The finite-type corollary, full
`ManuscriptTarget`, final PDFs and publication remain outside this mission.

## Quantifiers and native definitions

`Statement.lean` and `Geometry.lean` are unchanged. Both d and embedding dimension
N are arbitrary, including zero; no nonempty or positive-dimension premise is
added. `ProperComplexEmbedding` has the smooth embedding, properness, injective
native differential, smooth almost complex J, J²=-id and native Cauchy–Riemann
equation. It has no symplectic, metric, radial or flow output as an input.
`SteinReferenceConstruction.reference i` constructs the reference from this
embedding alone; `SteinTarget` outputs that reference before quantifying T.
`PackagedSteinTarget` separately applies to every reference satisfying the
literal original identities, not just this chosen construction.

Native Mathlib is checked first: `Diffeomorph.trans`, `coe_trans`, `symm` in
`Mathlib/Geometry/Manifold/Diffeomorph.lean` establish that F₂.symm.trans F₁ is
F₁∘F₂⁻¹; `mfderiv` is the actual tangent derivative; and
`Bundle.ContMDiffRiemannianMetric` carries the smooth positive definite bilinear
form. The pinned FsFltz `Geometry/Smooth.lean` uses native `TangentSpace`,
continuous alternating forms, `extDeriv` transported by chart derivatives,
actual derivative pullbacks, and `Diffeomorph`. `IsSmoothForm` is chart smoothness.
The existing algebra proves the scalar derivative, composition and inversion
laws for precisely these operations, including smooth forward/inverse isotopies.

Mandatory third reuse check: the archived cluster-skeleton 2c239b0 snapshot at
`/var/lib/archon-worker/imports/project-reference/archon_liouville/cluster-skeleton-2c239b0.tar.gz`
was inspected without editing it. `ClusterSkeleton/GeometryTarget.lean`:
`LiouvilleData` and `toCompleteLiouvilleManifold` preserve the actual primitive,
positive contraction and `CompleteLiouvilleFlow`; `GeometryNativeBridge.lean`:
`LiouvilleData.isMIntegralCurve` exposes the all-real native curve. These concern
cluster-specific carriers and complete Liouville data, so the current exact
symplectic application reuses the already delivered general theorem instead.
No new flow, metric or differential-form foundation is needed.

## Exact metric and growth bridges

R remains `steinRadius i = exp(1)+‖i.map‖²`. The primitive identity is
β=−(1/4)dR∘J. `SteinReference.induced_metric` fixes g literally to the real
Euclidean inner product of the differential of i. `compatible.metric_eq` fixes
g=dβ(.,J.). `CompatibleStructure.MetricTangent` equips the actual tangent vector
space with this g-norm; `covector` keeps the same linear function and installs
the g-dual norm. `inverseContraction` constructs the positive-contraction inverse
by finite-dimensional nondegeneracy; `inverseNorm` is its g-dual-to-g operator
norm. No chart norm may replace this norm.

`SteinRadial.metric_norm_eq` proves ‖v‖g=‖di(v)‖; `radius_dualNorm_sq` proves
‖dR‖g*²≤4(R−e). `reference i P` keeps EXACTLY P.exactStructure and P.compatible,
R=steinRadius i, c=1/4, rstar=2. The application will expose definitional
metric, dual-norm, inverse-norm and weak-taming equalities, rather than infer
norm compatibility from names. The radial inequality actually holds globally.
Properness and R≥1 come from `SteinRadial.radius_proper/radius_lower`.

Every original B, smooth only within [e,∞), is permitted. `SteinGrowth.extend`
constructs admissible growth on [1,∞) agreeing with B above e+2, with divergent
improper integral. `SteinGrowth.steinRadius_growth` requires properness and a
lower bound; both are supplied by the radial construction. It keeps g, T, R
and C, enlarging the compact exception by a compact radius sublevel. This
neither adds a global inverse bound nor restricts the primitive or its growth.
The common-reference inputs have independent existential B_i, C_i and compact
exceptions; they are not replaced by a shared growth witness.

## Proof integration and observable output

Apply delivered `MainComparison.mainTarget` to `SteinRadial.reference i P`
after the proved growth conversion. Apply the packaged result to the actual
constructed reference to prove source-level `SteinTarget`. Expose native
smooth diffeomorphism F, smooth h, identity isotopy with smooth inverse family,
F*λ=β+dh and F*dλ=dβ. An assumed `MainTarget` argument is not permitted.

For `CommonReferenceTarget`, apply the delivered main theorem twice and then
`ExactComparison.commonReference`. A separate explicit consumer extracts the
two actual witnesses and uses `ExactComparisonAlgebra.Witness.commonReference`
to expose Φ=F₁∘F₂⁻¹ and q=(h₁−h₂)∘F₂⁻¹ with the same complete identities and
isotopy. These are witnesses in the conclusion, not input certificates.

Neither the metric nor either primitive is assumed complete; no finite-type
hypothesis is added. Objects called Liouville still use FsFltz's actual smooth
`Flow ℝ` with the chart ODE at every real time and i_Z dλ=λ. No claim of
Liouville completeness follows merely from exact comparison.

Exact input bindings are in `verification/corollaries/import-manifest.json`;
reviewed semantic hashes and the managed compilation receipt accompany this
gate. Final proof acceptance requires its own exact-source checks, nonelided
inventory, native consumers and allowed-only transitive axiom audit.
