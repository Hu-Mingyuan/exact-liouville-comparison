# Independent statement-fidelity review

Verdict: **ACCEPT for the bounded pre-proof statement/crosswalk gate**.
Mission: `b518dc8e-9cf8-40a0-b7dd-1199bf9c17a3`, revision 1.
Reviewer: independent `/root/statement_review`; no corollary proof authorship or semantic edits.
This accepts the statements and definition correspondence, not a proof of the corollaries,
not a transitive axiom audit, and not completion of the manuscript.

## Exact reviewed bindings

All five current files match `statement-hashes.json`:

| File | SHA-256 |
|---|---|
| `ExactLiouvilleComparison/CorollaryComparisonStatement.lean` | `58d21d2d38721e4e9cb3194d2ba4b4793899359cb6f3501e4ae7663651581efa` |
| `docs/corollary-comparison-crosswalk.md` | `9e2094bee96a21d5e9dac8be984eb1143ec1278d20e1d217139c28f42071bde8` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |

Evidence SHA-256:

- `statement-hashes.json`: `34469944e135936f9b126e8c50d037806eb3b0828186cc0a0d20e427127b9b84`.
- `import-manifest.json`: `eb72774c4b4c89dee03dd5ae995cc415c9f62a1ce42a2de57f22169939d937b3`.
- `statement-build.txt`: `74a9b212dfd0adcbc4ae8ec7faf5576de61349da0ac53b60c79d71a103e9d4c6`.
- `lake-manifest.json`: `2790d3bafa974c7cbdd6e9ca85ac8e33d1caf801ab00d645ceebaea8aa65ba83`.
- `lean-toolchain`: `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b`.

Independently recomputed all 108 import-manifest SHA bindings against the working
files (102 distinct paths): no mismatch. Counts by private source commit are
88 at `55493c9ba47cc09071f6abf0b16b901a95f19b1f`,
9 at `4bb4bc2159d635b157f39a7d415cf2e63d491d4e`,
4 at `f02720d55df5ea4ae0e16058f3614d090e0d832e`, and
7 at `23046e70e5d55e308ec8d16a8a7aaaf7dd14c18b`.
The manifest contains every exact path/blob/SHA binding; it is not a claim that
this reviewer independently re-proved those 102 files.

The private commits are not available as local Git trees. I inspected
`scripts/import-corollary-inputs.py`, whose authenticated source retrieval checks
commit/path, the Git blob SHA-1, and exact existing bytes. Independently repeated
read-only authenticated API retrieval from repository
`31e09b7d-6080-4383-8e4e-92b14780690a` for MainComparison, SteinReference,
SteinRadial, SteinGrowthConsumers, and ExactComparisonAlgebra. All five returned
commit/path, blob hash, SHA-256 and bytes match the manifest and local files.
This independently samples all four source commits; the 108 local SHA checks are exhaustive.

Verified installed dependency HEADs: FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; toolchain is Lean 4.34.1.
The final managed statement receipt records command
`lake build ExactLiouvilleComparison.CorollaryComparisonStatement`, 3781 jobs,
returncode 0, `status: passed`, `ok: true`, `snapshot_verified: true`, and source key
`d8848793189cf8d83d73d4b66fa12a385d4d076a07ed204cce1be50559396010`.
I inspected that final receipt before issuing this verdict and ran no competing build.
The earlier deferred receipt is not the evidence used for acceptance.

## Source and complete-type coverage

Read AGENTS.md, docs/objective.md, the unchanged manuscript setup and Theorem
`thm:main`, equations `eq:steinsetup`/`eq:steinradial`, corollary `cor:stein`
with its proof, and `cor:two` with its explicit map/gauge proof. Read the complete
new statement and crosswalk. Followed their definitions backward through the
complete source-declared types, including implicit dimension/manifold/reference
binders, of:

- `PackagedSteinTarget`, `SteinTarget`, `CommonReferenceTarget`,
  `ConstructedSteinTarget`, `ExplicitCommonTarget`, and `MainTarget`;
- `ProperComplexEmbedding`, `SteinReference`, `RadialReference`,
  `AdmissibleGrowth`, `WeaklyTames`, `GrowthAtInfinity`;
- `ExactSymplecticStructure`, `CompatibleStructure`, its metric fiber/dual,
  positive flat map, constructed inverse, `inverseNorm`,
  `SmoothlyIsotopicToIdentity`, and `ExactComparison`;
- `SteinReferenceConstruction.reference/compatible/exactStructure`,
  `primitive_eq`, `exteriorDerivative_apply`, and the induced metric construction;
- `SteinRadial.radius_smooth/radius_proper/radius_lower`,
  `metric_norm_eq`, `radius_derivative/radius_dualNorm_sq`, and `reference`;
- `SteinGrowth.extend`, `extend_eq`, the divergent-integral bridge,
  `estimate_outside_enlarged`, `growthAtInfinity`, and `steinRadius_growth`;
- `MainComparison.mainTarget/exactComparison/comparisonWitness`;
- `ExactComparisonAlgebra.Witness`, `exactComparison_iff_exists_witness`,
  `Witness.comp/symm/commonReference`, and `ExactComparison.commonReference`.

There are no hidden typeclass nonemptiness, positive-dimension, completeness,
finite-type, supplied comparison, or supplied Moser-flow assumptions in the
reviewed target types. `MainComparison.mainTarget : MainTarget` has no extra
argument. Its more explicit consumer takes exactly the radial data, arbitrary
admissible G, weak taming, positive C, compact K and its outside-K estimate.
The conditional algebra laws legitimately take already proved comparisons;
`ExplicitCommonTarget` instead puts both witnesses in its existential conclusion.

## Positive mathematical correspondence

1. **Native geometry and domains.** `SmoothManifold d` is Hausdorff,
second countable and smooth over the full real model, without boundary;
`d : ℕ` and `N : ℕ` are arbitrary. The targets neither require inhabitedness nor
exclude zero dimensions. Properness is `IsProperMap`. No fixed affine-space
carrier replaces the manifold. `ProperComplexEmbedding` supplies smooth J,
J²=-id, the proper smooth topological embedding, injective actual tangent
map, and its Cauchy–Riemann equation. These are appropriate real differential
source data for the chosen proper holomorphic embedding. It assumes no metric,
symplectic form, radial bound, flow, or comparison conclusion. The proof may
use this slightly more direct real differential formulation without needing
an integrability assumption to derive the advertised comparison.

2. **Stein reference constructed from source.** `SteinTarget` existentially
outputs P before universally quantifying T. It does not smuggle the construction
in as an input. `ConstructedSteinTarget` fixes P to the delivered actual
`reference i`. The packaged target intentionally quantifies every reference
with the literal identities, and is separately labelled conditional. Inspection
of the construction shows its primitive is an actual pullback, its exterior
form and nondegeneracy are proved, and the metric is constructed from the
injective derivative. No circular field is present.

3. **Literal radius, sign and metric.** R is exactly exp(1)+the squared complex
Euclidean norm of the embedding. The primitive identity is exactly
β=−(1/4)dR∘J. The induced real Euclidean inner product of di is explicitly
identified with g=dβ(.,J.). `SteinRadial.reference i P` preserves P's actual
exact structure and compatible structure definitionally, keeps R, and supplies
c=1/4 and rstar=2. The radial bound is actually proved globally, so this choice
of compact core adds no premise. The stronger estimate
|dR|²≤4(R−e), properness, and lower bound all have actual supplied theorems.

4. **Norm semantics.** The native Riemannian metric is positive definite and
smooth. `MetricTangent` installs that metric's norm on the actual tangent vector
space. The covector map keeps the same linear function, with continuity proved
by finite dimensionality; its operator norm is precisely the g-dual norm.
`flatLinear` evaluates dλ(v,w), with positive contraction. The inverse is
constructed from nondegeneracy, with its contraction equation proved, and its
operator norm goes from g-dual to g. `metric_norm_eq` identifies this norm with
|di(v)|. Hence preserving `P.compatible` preserves the original norm appearing
in the hypothesis; it is not a silent switch to the chart norm.

5. **Every admissible growth and the compact exception.** The admissible B is
arbitrary, positive and dominating r on its half-line, smooth only within that
half-line, with the literal interval-integral primitive tending to +∞. The
Stein endpoint is e, not 1. The proved extension agrees with this B for r≥e+2;
it makes no analyticity, monotonicity or primitive-growth assumption. The
conversion keeps T, R, g and C and enlarges K only by the proper compact radius
sublevel. Thus the outside-compact hypothesis, including boundary points and
a possibly empty original K, is preserved. Weak taming remains ≥0 at every
point/tangent vector; symplectic nondegeneracy is separately required.

6. **Actual comparison conclusions.** `ExactComparison` gives an actual native
smooth diffeomorphism F, smooth h, the pointwise equality F*λ=β+dh and literal
pullback equality F*dλ=dβ. Its isotopy is a family of actual diffeomorphisms
on [0,1], with endpoints identity/F and jointly smooth forward and inverse
families. No support condition is imposed on h or the isotopy. The source
conclusion's differential-form identity is included explicitly, rather than
substituted for the stronger primitive conclusion.

7. **Common reference and exact formula.** The two `GrowthAtInfinity` premises
have independent existential B_i, C_i, K_i, and no shared witness is required.
Unfolding `Witness` gives exactly the same full comparison properties.
Native `Diffeomorph.coe_trans` confirms that F₂.symm.trans F₁ evaluates as
F₁∘F₂⁻¹. The gauge is literally (h₁−h₂)∘F₂⁻¹, with the sign and order in
`cor:two`. The existing witnessed algebra and both directions of
`exactComparison_iff_exists_witness` were inspected. The proposed output is
stronger only by exposing the independently obtained witnesses and the
exterior identity already entailed by the source, not by adding an assumption.

8. **Completeness terminology.** These are exact-symplectic applications;
neither the metric nor either primitive is assumed complete. Inspected the
pinned FsFltz `CompleteLiouvilleFlow`: an actual `Flow ℝ`, jointly smooth,
solving the chart ODE at every real t. `CompleteLiouvilleManifold` and
`CompletePrimitive` preserve the fixed primitive and positive contraction.
The new targets do not name an incomplete primitive a Liouville manifold or
claim completeness from a gauge change.

## Reuse and limits

Inspected actual pinned definitions in FsFltz Geometry/Smooth.lean,
Liouville.lean and FixedAmbient.lean, and Mathlib's native Diffeomorph
composition/inversion and ContMDiffRiemannianMetric. The form representation is
native continuous alternating tangent forms; its exterior derivative is native
`extDeriv` of chart coefficients transported by actual chart derivatives,
its scalar derivative is `mfderiv`, and its pullback uses the actual derivative.
Also inspected the unchanged archived cluster-skeleton 2c239b0 GeometryTarget
LiouvilleData/toCompleteLiouvilleManifold and GeometryNativeBridge
isMIntegralCurve. Those preserve the same primitive/field/all-real flow but
have cluster-specific carriers; they do not replace the general comparison
application. The crosswalk's reuse explanation matches these sources.

No statement repair is required. The crosswalk correctly marks specifications
as specifications and states the needed integration: use the delivered main
theorem after the proved radial and growth bridges, then the actual algebra.
This review does not itself discharge those integrations or independently
audit every imported proof. Final proof acceptance still requires the actual
corollary theorems, original-metric consumers, a nonelided declaration inventory,
exact-source build and allowed-only transitive axiom audit. The finite-type
corollary, full ManuscriptTarget, final documentation/PDFs and GitHub publication
remain outside this bounded verdict.
