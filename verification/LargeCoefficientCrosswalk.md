# Large radial coefficient: definition crosswalk

Scope: manuscript equations `Mn`, `A`, and `Aproperties` only. This construction
does not prove any Moser flow, comparison theorem, radial metric lemma, or phase
acceptance. Accepted `Geometry.lean` and `Statement.lean` remain byte-identical
to semantic source `46fccea69cb9524882bbeda83b0ac2067d22a149`, independently reviewed
in artifact `8930b2e3-ab88-498e-8a6f-d3f732fa8f95`. The unchanged scalar source is
`4bb94fa4a3d5f42b4107846cd2f9adb0758385d6`. No semantic interface changes are proposed.

| Manuscript object | Actual Lean object and proved bridge |
| --- | --- |
| Smooth one-form lambda | `M.Form 1`, `M.IsSmoothForm lam`, with the pinned FsFltz chart definition. No symplecticity of lambda is required. |
| lambda as a covector | `LargeCoefficient.oneCovector`, the inverse of Mathlib `ContinuousAlternatingMap.ofSubsingleton ℝ (M.Tangent x) ℝ (0 : Fin 1)`. `oneCovector_apply` proves its value is literally `evalOne lam x v`. |
| Explicit g-dual norm | `formNorm P.compatible lam x` is exactly `P.compatible.dualNorm x (oneCovector lam x)`. The metric is the accepted `P.compatible.g`, tied to d beta(.,J.) by `metric_eq`. |
| Finiteness on compact sets | `formNorm_locally_bounded` and `formNorm_bddAbove_on_compact`, proved from smooth lambda and the native smooth metric. No boundedness assumption is supplied. |
| Sublevel R <= rstar+n+1 | `sublevel P n`, proved compact by identifying it with `R` preimage of `[1,rstar+n+1]` and applying `P.proper_R.isCompact_preimage`. |
| M_n | `levels P lam n = 1 + sSup (formNorm ... '' sublevel P n)`. `sublevel_norm_bddAbove` prevents the unbounded-real-supremum fallback. `levels_empty` uses `Real.sSup_empty = 0`; `levels_mono` explicitly handles empty lower sublevels. |
| theta | Mathlib `Real.smoothTransition`, through unchanged `SmallCoefficient.chi`. This is the manuscript exp(-1/t) transition, not an abstract cutoff operation. |
| A | `A P lam = series (levels P lam) P.rstar`. `A_formula` displays the exact manuscript expression with j=n+1. |
| Locally finite sum | `series_locally_finite` / `A_locally_finite` prove a common finite range on a neighborhood of every real radius. `series_eq_sum` gives exact finite expansion. |
| Smoothness and core | `A_smooth` proves global `ContDiff ℝ ∞`, stronger than closed-ray smoothness. `A_core` proves constancy for all r<=rstar, hence on [1,rstar]. |
| A' >= 0, A >= 1, A+rA' > 0 | `A_monotone`, `A_deriv_nonneg`, `one_le_A`, `A_radial_pos`; derivative is native `deriv`. Positivity is asserted for r>=1. |
| Domination of lambda | `A_dominates`. For the core use M_0; outside use n=floor(R-rstar), sublevel domination and `series_ge_level`. The knot identity is proved by telescoping the finite sum. |
| A >= k | `k_le_A` composes unchanged `SmallCoefficient.k_le_one` with `one_le_A`. Only this comparison uses an `AdmissibleGrowth 1` input. |

## Native metric transport

The local norm proof uses `A.g.toRiemannianMetric.toCore` to equip the **native
tangent fibers** with `toNormedAddCommGroupOfTopology` and `ofCoreOfTopology`.
These preserve the native tangent topology. The local `hnorm` proof identifies
this norm with the accepted `A.MetricTangent x` norm: both are literally
`sqrt (A.g.inner x v v)`. Thus the operator-norm conclusion is the accepted
g-dual norm. A chart norm occurs only as an intermediate estimate.

Mathlib `eventually_norm_trivializationAt_lt` controls the norm of the map from
the g-normed fiber to the model chart. `TangentBundle.continuousLinearMapAt_trivializationAt`
identifies it with the actual chart differential. FsFltz
`SmoothManifold.formInChart_comp_chartTangentMap` reconstructs lambda exactly.
The chart coefficient is locally bounded because `IsSmoothForm` implies its
continuity on the open chart target. The resulting pointwise operator estimate
is then passed to Mathlib
`Bornology.isBounded_image_of_isLocallyBounded_of_isCompact`.

## Reuse and provenance

Search order was pinned Mathlib, pinned FsFltz, then the recorded cluster-skeleton
archive at `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`. Mathlib supplies the genuine
transition, native metric and bundle estimates, compactness, real suprema,
finite/infinite sums, derivatives and monotonicity. FsFltz supplies only the
existing smooth-form representation and its proved chart reconstruction.
Cluster `PrimitiveCutoffs.lean` uses the same Mathlib transition but contains no
general arbitrary-metric covector or compact-sublevel majorant theorem to reuse.
No upstream file or dependency pin was changed. The small coefficient remains
attributed to mission `f013dab4-6ac4-406e-b524-a18c0db7f73a`; the independent radial
metric mission `b52749be-7471-4774-92ed-7c623614bbee` is untouched.

The new modules isolate the minimal metric bridge, elementary step series, and
geometric consumer. `coefficient_properties` is a theorem with proof terms, not
a proposition or certificate assumption. `verification/LargeCoefficientConsumer.lean`
constructs a coefficient for an arbitrary accepted reference and smooth form,
checks interpolation against the delivered k, and checks empty manifolds.

Run `python scripts/verify-large-coefficient.py` for managed validation, exact
source hashes, elaborated types and transitive axiom checks. The receipt records
the actual outcome; this document alone is not proof acceptance.
