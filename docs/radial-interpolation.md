# Pointwise radial interpolation

This is the pointwise and scalar exhaustion portion of manuscript Lemma
`lem:bridge`. It proves no smooth dependence of the constructed vector, no
compact-core uniform estimate, and no trajectory existence or completeness.
Those obligations remain with root mission
`040e593e-7a38-4959-9158-1caffe4e49fa`.

## Fixed source and definition crosswalk

The exact base is radial delivery `b4585587a039a28362ab46285ccd3fe98f4655e1`
in repository `fe83a2bb-5147-4bfd-b750-19b11c583d74`, verified publication
`ee7e15d7-a0cd-40a9-94e5-1bca883356ce`, delivery artifact
`7a3d5a82-e828-4197-9451-fe145fdf9e3e`, checks
`66344d68-8824-4a19-8595-baee4ee92e11`.
The accepted Geometry/Statement source `46fccea69cb9524882bbeda83b0ac2067d22a149`
and independent statement/definition review
`8930b2e3-ab88-498e-8a6f-d3f732fa8f95` are preserved byte-for-byte.
The new definitions are additive constructions, not changes to the accepted
semantic interfaces. The base file identities appear in
`verification/radial-interpolation/base-source.json`.

All names below are in `ExactLiouvilleComparison.RadialInterpolation`, except
the explicitly named delivered interfaces and consumer namespace.

| Manuscript | Lean declaration and actual meaning |
| --- | --- |
| rho_u | `rho q₀ q₁ u r = (1-u)*q₀.rho r + u*q₁.rho r`. |
| delta | `delta q₀ q₁ r = q₁.rho r - q₀.rho r`. Ordering is required only for inequalities, not symplecticity. |
| Admissible interpolated coefficient | `coefficient q₀ q₁ u hu : RadialCoefficient P.rstar` constructs all fields from the input coefficients and `u ∈ Icc 0 1`. |
| rho_u_prime | Actual `derivWithin (rho q₀ q₁ u) (Ici 1)`, with `rho_derivWithin` and `coefficient_prime`; no extension below 1 is assumed. |
| mu_u | `primitive q σ = σ + q.primitive`, where q is the interpolated coefficient and the delivered primitive is literally `rho_u(R) beta`. |
| Weak taming of d sigma | `WeakDifferential σ` says `0 ≤ evalTwo (M.exteriorDerivative σ) x v (P.compatible.J x v)` for all x,v. It contains no nondegeneracy assumption. Smoothness is a separate `M.IsSmoothForm σ` hypothesis. |
| d mu_u symplectic | `exactStructure` constructs `ExactSymplecticStructure M`: smooth primitive, native closed exterior derivative and proved nondegeneracy. This is not a hypothesis package. |
| X_u(x) | `vector q σ hσ hw δ x : M.Tangent x` is the existing finite-dimensional `CompatibleStructure.inverseContraction` applied to `-δ(R) beta`. `vector_equation` and `vector_unique` prove existence and uniqueness for positive contraction in the first slot. The evaluated native parameter derivative is proved by `primitive_parameter_derivative`. |
| h_u, its tangent norm and dual norm | Exactly `q.compatible` from the delivered radial construction. Energy uses `@norm (q.compatible.MetricTangent x) _ X`; `differential_sq_le` uses its actual covector operator norm and the delivered `radial_dualNorm_sq`. No chart norm is used for any estimate. |
| a, D_u | Delivered `q.radialA x = c*abs(dR)_g^2` and `q.radialD x = rho_u(R)+rho_u_prime(R)*a`. The reference g is still `P.compatible.g`. |
| Q_u(r) | `Q q₀ q₁ u r = r*rho q₀ q₁ u r`. Partial derivatives and the chain rule along an arbitrary differentiable scalar curve are native `HasDerivWithinAt` / `HasDerivAt` statements. |

The original independent review is reused for the unchanged main statement and
native geometry. Any supplementary additive crosswalk assessment is advisory
and is recorded separately; it is not full-theorem or phase acceptance.

## Proof map and boundary cases

`rho_hasDerivWithinAt` and `rho_derivWithin` use Mathlib's constant-multiple
and addition rules, including r=1. The constructed coefficient proves smoothness,
positivity, constant core and radial positivity. The delivered
`rhoPrime_eq_zero` applies to this coefficient on the whole closed core
interval, including r=1 and r=rstar; the generic `core_derivative` consumer
checks this. Parameter endpoints u=0,1 are included in the construction.

`exteriorDerivative_add` proves the intrinsic sum rule from the actual pinned
chart definition and Mathlib `extDeriv_add`. `differential_apply` identifies
the differential of the primitive. `nondegenerate` tests a hypothetical kernel
vector against Jv: the radial metric contribution is strictly positive for
v nonzero and the sigma contribution is nonnegative. Smoothness and closedness
follow from the pinned intrinsic exterior calculus, so d sigma may be zero.

`vector` uses the accepted finite-dimensional inverse contraction, whose
existence was proved from injectivity and equal finite dimensions. It is not
an assumed Moser field or flow. `primitive_parameter_derivative` proves, on
every native tangent vector, that the actual parameter derivative of the
interpolated primitive is delta(R)*beta, identifying the contraction right side
with minus that derivative. Evaluating its contraction equation on JX and
using beta=-c dR composed J and J squared=-id proves `energy`, exactly
`bridgeenergy`. `vector_eq_zero` handles delta(R)=0 globally.

`differential_sq_le` applies the operator norm inequality in the actual h
metric and substitutes the delivered sharp dual identity a/(cD). `radial`
proves `bridgeradial`: first zero delta, then nonnegative Y=-XR from energy,
then Y squared ≤ (delta*a/D)*Y. Its Y=0 branch avoids division by Y.
Only the proved-positive c and D are canceled; neither delta nor dR is inverted.

`Q_directional` multiplies the radial bound by rho+R*rho_prime > 0,
proves the rational identity and obtains
`delta*rho*(R-a)/D ≤ delta*R+(rho+R*rho_prime)*XR` and nonnegativity
of the left side. `Q_curve_derivative` supplies the native scalar chain rule
at every exterior radius. It assumes only a differentiable scalar curve and
does not assume any geometric trajectory. `Q_lower` and `uniform_exhaustion`
prove the scalar exhaustion: each level L has a T≥1 valid for every u∈[0,1]
and every r≥T whenever r*rho₀(r) tends to infinity.

The generic consumer module `RadialInterpolationChecks` proves symplecticity
and unique solvability at every point, compact-core derivative vanishing, the
literal sigma=0 energy/radial estimates, equal-coefficient zero vectors, and
vanishing at an exterior critical point dR=0. The `scalar_barrier` consumer
combines the native scalar derivative with the directional inequality under
the explicit hypothesis f'(u)=dR(X), without asserting such a curve exists. No consumer assumes a solution,
inverse, nondegenerate d sigma, or complete flow.

## Reuse audit in the required order

1. **Mathlib** `d13f23b723b8a846827a245b89c10fc7d3f11612`: inspected
   `Analysis/Calculus/Deriv/Add`, `Deriv/Mul`,
   `Analysis/Calculus/DifferentialForm/Basic`,
   `LinearAlgebra/BilinearForm/Properties` and
   `Analysis/Normed/Operator/Basic`. Directly use
   `HasDerivWithinAt.const_mul/add/mul/derivWithin/hasDerivAt`,
   `HasDerivAt.comp/mul`, `uniqueDiffOn_Ici`, `extDeriv_add`,
   `ContinuousLinearMap.le_opNorm`, `sq_le_sq₀`,
   `tendsto_atTop` and `eventually_atTop`. Native derivative and
   operator-norm definitions are not replaced.
2. **FsFltz** `1a3d387cfacc746e25aad31e5b27b1803103e7cb`: inspected
   `Geometry/Smooth`, `SmoothForms`, `ExteriorDerivative` and the
   sum-rule proof in `RankTwoLiouville.evalTwo_exteriorDerivative_rankTwoPrimitive`.
   Reuse `SmoothManifold.Form/Tangent/exteriorDerivative/Nondegenerate`,
   `IsSmoothForm.add`, `isSmoothForm_zero`,
   `isSymplecticOn_exteriorDerivative_iff`, `evalOne/evalTwo` and
   `scalarDerivative`. The missing general intrinsic additive statement is
   a narrow proved bridge from `formInChart_add` and `extDeriv_add`.
3. **cluster-skeleton** `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`:
   inspected the actual read-only archived source at the provenance path in
   the existing accepted `verification/cluster-access.json`.
   `ClusterSkeleton.TorusLiouvilleDynamics.native_equation_exists`
   proves positive contraction solvability from nondegeneracy, using finite
   dimensionality and the native one-form/dual equivalence. The accepted
   `CompatibleStructure.inverseContraction` already generalizes this to
   arbitrary right-hand covectors with explicit metric norms, so it is reused
   unchanged. The cluster radial dynamics results concern its torus/seed
   model and do not supply this general radial interpolation inequality.
4. New infrastructure is restricted to coefficient interpolation, the narrow
   native sum-rule bridge, weak-differential predicate, explicit constructions,
   and pointwise/scalar estimates. All delivered source and attribution remain
   intact, including the separate algebra owner `a7458327`.

## Verification and delivery

Run `python scripts/verify-radial-interpolation.py`. It checks the exact base
hashes and pins, compiles the bounded consumer, prints complete elaborated
declaration types, and audits all listed declarations transitively, allowing
only `propext`, `Classical.choice`, `Quot.sound`. Final receipts require
`snapshot_verified=true`; development passes without that flag are not
exact-source receipts. A private Forge publication binds the audited new-file
hashes to the delivered exact commit, preserving unchanged base tree entries.

Mission `2e441ab2-0646-49f4-9152-2fb7bd7f2747` owns this bounded source
delivery and concrete repairs. Root retains full-proof incorporation/recovery.
No aggregate import, manuscript, pin, upstream source, old project, GitHub
repository or final PDF is changed by this delivery. No mission criteria were
removed or strengthened.

## Operational notes

All Lean invocations were serialized through the managed helper. The first
preparation resolved missing auxiliary pinned source packages in the inherited
dependency path; its log reported small Git clones. No manual dependency
download, source edit, cache clearing, service restart or capacity change was
performed. Subsequent checks reuse these dependencies. The temporary host
memory safeguard (notice 0dd3959c-a106-4095-a520-463b10ca0394) was read and
acknowledged; the native crosswalk helper performed read-only inspection and
no compilation. Development snapshots without a Git context were explicitly
not treated as exact-source acceptance.
