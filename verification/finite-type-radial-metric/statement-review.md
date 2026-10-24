# Independent statement-fidelity review

**Verdict: PASS — bounded specification and definition crosswalk only.**

Reviewer: independent `metric_review` agent for mission
`0b5b2f0c-3dfa-4741-ac55-30976cabd107`, 2026-10-24. Baseline:
`f8b5b6bcb56a18c0094d15fed4619ff100327e30`. Applied the supplied
`subagents/reviewers/statement-fidelity.md` rubric by inspecting the actual
definitions, quantifiers, source conventions, and boundary cases. No repairs
to this statement or crosswalk are required. This is not acceptance of a proof
of `Target`, radius existence, `FiniteTypeTarget`, or the main comparison theorem.

## Source and scope

The precise source is the proof of `cor:liouville` in
`docs/reference/exact_liouville_comparison.tex`, lines 402–409, with cylindrical
conventions in lines 375–386. The source asserts
`lambda_0 = -dr composed with J` and `|dr|_g^2 = r`, with
`g = d lambda_0(., J.)`. It then separately constructs a proper smooth radius
equal to `r` for `r >= 2`. The reviewed target isolates the first calculation
for any supplied smooth extension of that radius. Its strict tail
`t > log 2` corresponds to the main theorem's required `R > rstar`, with
`rstar = 2`; it does not claim the radius construction or global comparison.
Omitting properness, a global lower bound, weak taming, and inverse-form growth
from this local calculation is intentional and mathematically justified.

## Fully explicit target type and assumptions

The compiled source declares `EndRadius` and `Target` as definitions of
propositions. Expanding the inferred binder types gives the following complete
mathematical type (the native manifold instances come from the supplied data):

```lean
∀ (d : ℕ) (D : FsFltz.Geometry.LiouvilleDomain d)
  (C : FsFltz.Geometry.Completion D)
  (A : ExactLiouvilleComparison.CompatibleStructure
    (ExactLiouvilleComparison.completionReference C)),
  ExactLiouvilleComparison.CylindricalStructure C A →
  ∀ R : C.ambient.manifold.Point → ℝ,
    ContMDiff (𝓘(ℝ, FsFltz.Geometry.Model d)) (𝓘(ℝ, ℝ)) ∞ R →
    (∀ (y : D.domain.boundary.Point) (t : ℝ),
      2 ≤ Real.exp t → R (C.endMap (y, t)) = Real.exp t) →
    ∀ (y : D.domain.boundary.Point) (t : ℝ), Real.log 2 < t →
      (∀ v : C.ambient.manifold.Tangent (C.endMap (y, t)),
        FsFltz.Geometry.SmoothManifold.evalOne C.ambient.primitive
          (C.endMap (y, t)) v =
        -C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
          (A.J (C.endMap (y, t)) v)) ∧
      (A.dualNorm (C.endMap (y, t))
        (mfderiv (𝓘(ℝ, FsFltz.Geometry.Model d)) (𝓘(ℝ, ℝ))
          R (C.endMap (y, t)))) ^ 2 = R (C.endMap (y, t))
```

There are no implicit extra hypotheses restricting the dimension or requiring
nonemptiness. `d : ℕ` is arbitrary; neither a positive-dimensional hypothesis
nor a fixed affine model replaces the manifold. `SmoothManifold d` supplies a
Hausdorff, second-countable native smooth real manifold without boundary,
modeled on `EuclideanSpace ℝ (Fin d)`. The boundary of the compact domain is
modeled on dimension `d - 1`; its points are empty when `d = 0`. Thus the local
end conclusion is correctly vacuous in that case, without making the
positive-dimensional statement vacuous. The conclusion quantifies every
ambient tangent vector, not only specified end-coordinate vectors.

`EndRadius` contains only pointwise values of the supplied `R`. It has no
derivative, metric estimate, norm identity, local inverse, flow-identification
bridge, or conclusion field. Its stronger equality at the endpoint is exactly
what the radius extension in the source supplies. Smoothness is native
`ContMDiff ... ∞`, not analyticity. No metric completeness is requested.

## Definition crosswalk checked against actual sources

1. `Statement.completionReference` retains the same ambient manifold,
   primitive, smoothness, and actual exterior derivative symplecticity.
   `CylindricalStructure` uses native `mfderiv C.endMap` and encodes
   `J(v,s) = (contactJ(v) + s Reeb, -alpha(v))` after pushforward for `t >= 0`.
   Its Reeb normalization, kernel condition, and horizontal contact operator
   match the source's cylindrical convention. `contactJ` is independent of
   `t`; compatibility and `J² = -1` belong to the original `A`. The primitive
   is fixed by the actual `Completion.end_primitive` equation as
   `exp(t) alpha(v)`. In particular, the minus sign in the target is correct.

2. Pinned `Smooth.lean` defines `Tangent` as native `TangentSpace`, forms as
   continuous alternating maps on those tangent fibers, and
   `scalarDerivative R x v` as precisely `mfderiv ... R x v`. The exterior
   derivative is the actual chartwise `extDeriv` transported by actual chart
   derivatives. It is not an arbitrary operation supplied to this target.

3. `Geometry.CompatibleStructure.g` is
   `Bundle.ContMDiffRiemannianMetric ... ∞`, whose inspected Mathlib definition
   contains a smooth positive definite symmetric fiberwise inner product.
   `metric_eq` fixes it to `d beta(v,Jw)`. `MetricTangent` uses the same vector
   space with `g.toRiemannianMetric.toCore` and the associated normed-group
   instance. `covector` uses finite-dimensional continuity to transfer the
   native linear functional to that metric norm without changing its values;
   `covector_apply` is `rfl`. `dualNorm` is the operator norm of this transferred
   covector into the usual real norm. It is therefore the actual g-dual norm,
   not the default/chart norm of `mfderiv`. The reviewed target does not take
   the desired norm equality as an input or replace it with an estimate.

4. Pinned `CompleteLiouvilleManifold.contraction` is
   `d beta(Z,v) = beta(v)`, the positive convention. Its `completeFlow` is
   `CompleteLiouvilleFlow manifold field`, whose `flow : Flow ℝ M.Point` has a
   jointly smooth action and `solves` asserts the chart ODE for every
   `(x : M.Point)` and every `(t : ℝ)`. It is an actual all-real-time flow,
   not a semigroup, local flow, or completeness label. `Completion.end_flow`
   identifies `endMap(y,t)` with this flow applied to the boundary inclusion.
   `FixedAmbient.CompletePrimitive` was also inspected; its conversion retains
   the prescribed primitive and this actual complete-flow interface. There is
   no Moser flow or comparison assumption in the reviewed target.

5. The crosswalk's stated tangent-surjectivity route exists at the pin:
   `BoundarySmooth.lean`, `Completion.endMap_isLocalDiffeomorph`, lines 110–142.
   The proof handles `d = 0` via `zero_boundary`, and otherwise obtains
   surjectivity from `end_immersion` and equality of finite dimensions. It uses
   native manifold derivatives. This is a proved upstream theorem, not an
   additional field smuggling the target conclusion into the inputs. Importing
   or applying it, and deriving the needed derivative bridges, remain work for
   the actual proof module.

## Noncircularity and remaining proof obligations

The specification is mathematically sufficient for the local calculation.
Differentiating the literal radius equality on an open tail neighborhood must
give `dR(d endMap(v,s)) = exp(t) * s`. The cylindrical identity and primitive
formula then give the first conclusion, using tangent surjectivity. The flow
ODE must identify `d endMap(0,1)` with the actual Liouville field `Z`.
The positive contraction and the first identity yield
`g(Z,v) = beta(Jv) = dR(v)`, while cylindrical normalization gives
`g(Z,Z) = exp(t)`. A genuine metric-dual norm argument then gives the squared
norm conclusion. These are proof obligations, not supplied bridges or a claim
that their Lean proofs already exist. In particular, equality on a closed
tail alone is not silently treated as a derivative equation at an endpoint.

I found no missing indispensable condition, strengthened assumption beyond
the stated local task, circular conclusion field, or counterexample separating
the reviewed type from that local source calculation. `Statement.lean` and
`Geometry.lean` have no diff against the baseline, and the inspected pinned
dependency files have no working-tree modifications.

## Compilation and acceptance limits

The supplied managed receipt `statement-build.log` ends with a successful
build of `ExactLiouvilleComparison.FiniteTypeRadialMetricStatement`, return
code 0, `snapshot_verified: true`, source key
`fcf7dd7731d9a93db5d739913a1b715c5d420fccba42e2a998b8f531b64699cd`, and
Lean 4.34.1. Its earlier out-of-date diagnostic is followed by a successful
rebuild, not hidden as a clean initial attempt. No extra build was needed for
this review. The FsFltz and Mathlib working-tree HEADs match their manifest
pins: respectively `1a3d387cfacc746e25aad31e5b27b1803103e7cb` and
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This PASS opens substantive work on this bounded target only. A final
source-bound proof review, consumers, successful managed proof build, full
declaration inventory, and allowed-only transitive axiom audit remain required.
This review is not a transitive axiom audit and does not certify the main theorem.

## SHA-256 source binding

| Source | SHA-256 |
|---|---|
| `ExactLiouvilleComparison/FiniteTypeRadialMetricStatement.lean` | `19e07aded10817181abdf3b74effff7c29a2f3dd1dda6e2c45e8dbfb1356cbad` |
| `docs/finite-type-radial-metric-crosswalk.md` | `b5ac34f09ac0f4113de20a10838d4eca69ee11554b32180e785c11fb94c47d72` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `docs/objective.md` | `0f7ca4a2449cca3d400e7afda913364582be71f858fe31475fa60665502ce5e8` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Liouville.lean` | `d51b04337e39b31ab1b1d3b20093ba5956b8ea0b04456e141ef4c827268b335e` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| `.lake/packages/fsfltz/FsFltz/Geometry/FixedAmbient.lean` | `8fcedb064de005c2d236a425cebcbd0dfc137c8f102070592cb5eef9efb60d16` |
| `.lake/packages/fsfltz/FsFltz/Geometry/BoundarySmooth.lean` | `f7e0bf01311b03f66f3a811cb6685708ca4fd1a4d131ea790fca3ce14c6e3b56` |
| `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` | `044b397c80cc85430415afd4f976195943dd0015170cd0388d445dc09098c979` |
| `verification/finite-type-radial-metric/statement-build.log` | `d154c9ce1fc32b933bffdd4675f50f4a9091677172d4a44c33bee67b1044f9ca` |
