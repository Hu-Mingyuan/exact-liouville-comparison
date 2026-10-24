# Independent first-path flow statement review

Reviewer: delegated independent agent `flow_statement_review`, 2026-10-23.
Scope: the new bounded first-path flow contract and its definition crosswalk,
before substantive flow proof work. Existing radial and first-path estimates
are inputs to this review, not re-reviewed here. No Lean source was changed and
no new build was run by this reviewer.

**Assessment: PASS for the statement/definition gate.** There is no blocking
meaning error, vacuous flow condition, added geometric hypothesis, or assumed
flow in `Target` or `GrowthTarget`. This accepts a specification for subsequent
proof work only. It does not accept flow existence, smooth dependence, the
Moser pullback identities, or the full comparison theorem as proved.

## Exact reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/FirstPathFlowStatement.lean` | `2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217` |
| `verification/first-path-flow/crosswalk.md` (corrected final version) | `d674b0bf9332be07bade8575f2940d2fc4db8679fa59e540f9a3207b07a17d75` |
| `verification/first-path-flow/statement-build.json` | `9c1828dea6f540500edaf572fea24f6dc90cb9eb27738604294bdbc5418c66ed` |
| `docs/objective.md` | `0f7ca4a2449cca3d400e7afda913364582be71f858fe31475fa60665502ce5e8` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/MoserRegularityStatement.lean` | `fecaeb5bfe5e16df859c8805915e525cca0ddbbe084f0c0649dc9532e6c9eb0b` |
| `ExactLiouvilleComparison/MoserRegularityFields.lean` | `8ef90c4df28f103792ee415afa2ad21b3a398a9c3ad8cb3675b83da371146370` |
| `ExactLiouvilleComparison/MoserRegularityGlobal.lean` | `81c7ee5fc61973bd82ad60c7cc5566e1ad28d0213753e91ec9cb9f2a8f0c30a7` |

The supplied build receipt reports successful compilation of
`ExactLiouvilleComparison.FirstPathFlowStatement` with Lean 4.34.1 and snapshot
verification. This is compilation evidence, not an inhabitant of either target.
The base-source receipt records direct API verification against private commit
`639183b158c1d05af687823fd3bc6a57c10fa4af`; the old sandbox Git HEAD is not treated
as the reviewed base. I inspected local declaration bytes and that supplied
receipt, without independently repeating its authenticated API requests.

## Definition and assumption findings

1. `Parameter` is literally `Set.Icc (0 : ℝ) 1`, and `parameterInterval` is
   `Icc 0 1`. `IsSolution` uses the actual native `HasMFDerivWithinAt` with
   derivative `r ↦ r • Z_t(γ(t))`. This is the nonautonomous counterpart of
   Mathlib's actual `IsMIntegralCurveOn` definition. The explicit continuity
   conjunct is harmless. For a general set `J` the ODE is required only at
   `J ∩ [0,1]`, because the field is interval-indexed; every use in `Evolution`
   has `J ⊆ [0,1]`, so that guard creates no vacuity.

2. `solves` covers every initial time and initial point and all terminal times,
   including 0 and 1, using within derivatives at endpoints. `agrees` and
   `initial` force the curve to start at its prescribed point.
   `unique` uses `uIcc s.val t.val`, so it also covers `t < s`. The degenerate
   case `s = t` merely recovers the identity statement; it does not assert
   impossible derivative uniqueness on a singleton. Applying `unique` to
   restricted curves gives pointwise uniqueness throughout the segment.

3. `M.SmoothEquiv M` unfolds to the native Mathlib `Diffeomorph` at regularity
   `∞`. Thus `map s t` is already an actual bijection with smooth inverse.
   `compose` has the correct order for an evolution from initial time to final
   time, and `inverse` identifies its native inverse with reverse evolution.
   `chart_solves` uses `M.chartTangentMap`, which is the actual `mfderiv` of the
   selected chart. Its chart-source premise ensures validity at that point;
   continuity gives the local chart domain needed for the within chain rule.
   It does not assert a derivative for a chart outside its source.

4. `smooth` asks for one extension smooth on an actual open subset of
   `ℝ × (ℝ × M.Point)` containing the whole closed time square times the
   manifold. It supplies joint dependence on both times and the initial point,
   including endpoint neighborhoods, without a uniform exterior time strip.
   Off that open subset the total extension has no required geometric meaning.
   `SmoothlyIsotopicToIdentity` unfolds to an actual family of diffeomorphisms
   with joint smoothness of both maps and inverses on `[0,1] × M.Point`, with
   identity and the requested map at the two ends. `isotopy` therefore has the
   advertised meaning, rather than asserting only a path of arbitrary maps.

5. `Target` retains every admissible growth witness, positive constant, and
   arbitrary compact exception in the original inverse-form bound.
   `GrowthTarget` takes the unchanged existential `GrowthAtInfinity` and
   outputs a growth witness together with its actual first-path evolution.
   The witness controls the chosen coefficient; it is not an unrelated field.
   Neither target takes an evolution, a continuation theorem, completeness of
   the metric, a primitive-growth estimate, or complete Liouville data as an
   input. They concern bounded nonautonomous exact-symplectic evolution, not
   all-real Liouville completeness.

6. `firstField` unfolds literally to `FirstPath.X P G T hw x t.val
   t.property.1`. The inspected proof of `first_intervalSmooth` uses its
   contraction equation with right side `-k(R) β`, matching the manuscript's
   `ι_X(ω + tη) = -kβ`. `WeaklyTames` is nonstrict. The explicit metric is
   `P.compatible.g`, with `metric_eq` identifying it with `dβ(.,J.)`.
   `MetricTangent`, `Dual`, and `inverseContraction` put the inverse positive
   contraction operator between the metric dual and metric tangent spaces.
   `inverseNorm` is their actual continuous-linear-map operator norm.
   The original crosswalk used the nonexistent field name `metric`; the parent
   corrected it to `g` during review. No Lean statement correction was needed.

## Required proof bridges and limits of this pass

`first_intervalSmooth` produces a single real-indexed extension whose vector
coefficients are smooth on open neighborhoods in every chart, by the actual
`IsSmoothIntervalVectorFieldFamily` / `SmoothNearInterval` definitions.
The pinned `contMDiffAt_familySection_of_chart` converts the coefficient germ
at any point in such a neighborhood to the actual tangent-bundle section.
To obtain a native open neighborhood, retain those chart neighborhoods,
intersect their inverse images with the corresponding chart sources, and
take their union. The single extension is already common, so no conflicting
field definitions need to be glued.

`NativeJoint` alone gives `ContMDiffAt ∞` at each required point, not the
explicit open neighborhood of joint smoothness required by continuation.
In particular, it is not legitimate simply to assert a common smooth open
neighborhood from those pointwise hypotheses. The crosswalk correctly makes
the stronger bridge from `first_intervalSmooth` a proof obligation.

`first_growth_consumer` supplies the literal first field, proper exhaustion,
boundedness below, and a uniform absolute bound on the actual derivative.
This is the correct scalar input for compact confinement in both time
directions. It produces neither curves nor smooth dependence. A generic
continuation prerequisite must prove actual finite-interval solutions from
the native open neighborhood and these scalar bounds. The pinned
`CollarFlow.contMDiff_joint_of_hasMFDerivAt` was also inspected: it requires a
globally smooth real-time field and already constructed all-real solutions.
Those hypotheses cannot be assumed for this bounded first-path field.

The manuscript's first-path full-interval assertion is faithfully represented
by this output contract. Construction of every `Evolution` field, native/chart
derivative compatibility, endpoint regularity, and later exact Moser identities
remain proof work. A theorem conditional on an unconstructed `Evolution`
would not discharge this target. This gate does not replace final exact-source
build receipts, interface consumers, or transitive axiom audits.

## Additional bounded prerequisite statement assessment

At the parent's request I also inspected
`ExactLiouvilleComparison/ODEContinuationStatement.lean`, SHA-256
`d1f8ad17b89f7acea0a9c757319bcfc027666df264c9471ba01d0c03164598f1`.
Its `FiniteIntervalExistenceTarget` passes mathematical statement review.
It takes an actual real-time tangent field smooth on a specified open
neighborhood of `[0,1] × M.Point`, a smooth proper bounded-below scalar, and
the absolute scalar derivative bound only on the closed interval. It outputs
an actual curve through every initial time and point. There is no hidden
existence, uniqueness, smooth-dependence, or continuation certificate input.

Its conclusion uses full `HasMFDerivAt` at both endpoints, stronger than the
within derivative needed by `Evolution.solves`. This is mathematically
appropriate: once the curve reaches an endpoint, the open neighborhood and
local ODE theorem extend that individual curve slightly past the endpoint.
No uniform extension time over all initial points is asserted. The bounds
outside `[0,1]` are unnecessary for those local extensions. The resulting
total function may be defined arbitrarily away from the relevant extended
interval. This assessment adds no proof of that construction and does not
certify a compilation receipt that was still pending when the file was read.
