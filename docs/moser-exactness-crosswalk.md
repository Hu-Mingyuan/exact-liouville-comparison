# Moser exactness definition crosswalk

Mission 1f6c4a8d-7d2b-4696-9a6f-2d9ac61c120b, revision 1.
Baseline f8b5b6bcb56a18c0094d15fed4619ff100327e30; roadmap
`docs/sdu-continuation.md` at that exact revision. Authoritative source:
`docs/reference/exact_liouville_comparison.tex`, lines 345–360, eq:exactness.
The two `*ExactnessStatement.lean` files contain contracts only. No proof of
Cartan, integral smoothness, endpoint exactness or the first-path consumer is
claimed at this statement gate.

## Actual definitions and signs

* `SmoothManifold d` (FsFltz/Geometry/Smooth.lean) bundles a Hausdorff,
  second-countable native Mathlib smooth manifold modeled on EuclideanSpace
  ℝ (Fin d), without boundary. Its tangent is exactly `TangentSpace`, its
  forms are dependent sections of `ContinuousAlternatingMap`. No affine-space
  restriction is made.
* `formInChart` transports each argument through the actual inverse-chart
  `mfderiv`. `exteriorDerivative` is Mathlib `extDeriv` of these coefficients
  transported back through chart `mfderiv`; `scalarDerivative` is actual
  `mfderiv` to ℝ. `pullback` uses actual `mfderiv` of the map. None is an
  arbitrary operation supplied by the theorem.
* `IsSmoothFormFamily` and `IsSmoothIntervalVectorFieldFamily`
  (FsFltz/Geometry/Family.lean) require joint C∞ coefficients on genuine open
  neighborhoods of [0,1] times each chart target. Extensions need not exist
  on a uniform larger time interval. The latter includes a real-parameter
  extension agreeing with the interval-indexed field.
* `FirstPathFlow.Evolution` (FirstPathFlowStatement.lean) supplies native
  diffeomorphisms `map initialTime terminalTime`, an open jointly smooth
  extension in both times and space, identity at equal times, native
  `HasMFDerivWithinAt` ODE on [0,1], chart ODE, uniqueness, composition,
  inverses and isotopy. This is a legitimate input to the generic calculus
  theorem; the first-path target uses the proved `FirstPathFlow.evolution`.
* `Equation` says dμₜ(Xₜ,v) = −∂ₜμₜ(v). The evaluation uses positive
  contraction, with X in the first slot. `CartanDerivative` states the full
  identity with the positive contraction and positive spatial differential
  terms. `PullbackDerivative` is its Moser cancellation. Both use within
  derivatives at the closed interval endpoints.
* `contractionAlong` is μₜ(Xₜ)(Gₜ(x)) with Gₜ = map 0 t. `gauge` is literally
  its interval integral from 0 to 1. The `if` extends an interval-indexed
  integrand to zero outside [0,1]; no cutoff, arbitrary primitive or alternative
  gauge is used. The integral does not depend on this outside value. Its
  smoothness and the commutation of spatial differentiation with integration
  are proof obligations, not fields or premises.
* `Endpoint` requires actual global `ContMDiff` smoothness of this gauge,
  pointwise covector equality G₁*μ₁ = μ₀ + dH, and equality of the pulled-back
  exterior derivatives. Evaluation on all tangent vectors is literal equality
  of one-forms. The endpoint map is the existing smooth diffeomorphism.
* `FirstPathExactness.primitive` is λ + t k(R)β using the delivered
  `SmallCoefficient.k` and `radialPrimitive`. The field is exactly
  `MoserRegularity.firstField`, definitionally the delivered `FirstPath.X`.
  Its equation and primitive/exterior-derivative bridge must be proved.
  The consumer retains arbitrary admissible B, positive C, original compact
  exception, weak taming, and unrestricted primitive growth. There are no
  new flow, completeness, smoothness, Cartan or exactness assumptions.
* The reference metric remains `P.compatible.g`, literally dβ(·,J·).
  Existing `MetricTangent`, `Dual`, `covector`, `inverseContraction` and
  `inverseNorm` supply its tangent, dual and operator norms in the input.
  This calculus step needs no metric bound of its own. All terminology here
  is exact symplectic; no incomplete flow is called a Liouville manifold.

## Mandatory reuse inspection, in order

1. Pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612:
   `Analysis/Calculus/DifferentialForm/Basic.lean` provides `extDeriv`,
   `extDeriv_pullback` (differentiable coefficients, C² map), and
   `extDeriv_extDeriv`; `DifferentialForm/VectorField.lean` supplies
   `extDeriv_apply_vectorField` with differentiable coefficient/field premises.
   Native `MFDeriv` and `ContMDiff` represent geometry and regularity.
   `Analysis/Calculus/ParametricIntegral.lean` supplies
   `hasFDerivAt_integral_of_dominated_of_fderiv_le` and its interval version
   with measurable, integrable, local derivative and domination hypotheses.
   These must be discharged using compact time and local chart neighborhoods.
   `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` supplies endpoint
   FTC with continuity and integrability premises. No native manifold
   time-dependent pullback/Cartan or C∞ parameter-integral theorem was found.
2. Pinned FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb:
   `Geometry/ExteriorDerivative.lean` proves
   `exteriorDerivative_eq_in_chart`, `formInChart_exteriorDerivative`,
   `isSmoothForm_exteriorDerivative`, `exteriorDerivative_exteriorDerivative`,
   and `exteriorDerivative_pullback` for smooth maps and smooth forms.
   `Geometry/FamilyLiouville.lean` proves
   `exteriorDerivative_eq_in_chart_of_contDiffAt` and
   `contDiffOn_spatialExtDeriv`, accommodating nonuniform open extensions.
   `Geometry/Family.lean` supplies the family definitions above. No Cartan or
   smooth parameter-integral theorem was found in these interfaces.
3. Cluster source inspected read-only at
   `/var/lib/archon-worker/imports/project-reference/archon_liouville/cluster-source-2c239b0/Hu-Mingyuan-cluster-skeleton-2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`.
   `ClusterSkeleton/TorusPrimitive.lean` and `GlobalTwoForm.lean` use the
   Euclidean `extDeriv_pullback`. Searching the source found no Cartan or
   integral-gauge theorem that supplies the missing bridges. Its
   `GeometryTarget.lean` is consistent with the complete-Liouville convention;
   that specialization is not required by this bounded exact-symplectic step.

## Proof obligations and integration ownership

The parent mission owns this contract, first-path premise discharge and final
integration. Missing proofs are: native time-dependent Cartan identity,
chart-local differentiation under the integral and C∞ gauge smoothness,
endpoint FTC and exterior-derivative consequence, and the unconditional
first-path consumer. A compiled target alone does not satisfy any of these.
No accepted semantic file, upstream dependency, manuscript, ThirdPath file or
ExactComparisonAlgebra file is changed.
