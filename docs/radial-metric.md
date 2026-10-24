# Radial metric lemma

This delivery concerns manuscript Lemma `lem:metric` and its generic first-path linear consumer. It constructs the exact symplectic form and a smooth native Riemannian metric with the original `J`. It does not construct the special scalar coefficients, a Moser flow, a complete Liouville flow, or the comparison diffeomorphism. No completeness hypothesis is added.

The source baseline is accepted semantic commit `46fccea69cb9524882bbeda83b0ac2067d22a149`, independently reviewed in artifact `8930b2e3-ab88-498e-8a6f-d3f732fa8f95`. Additive linear delivery `fb94841b094b171df6744146e39d9cc2204fe002` is the publication parent (verified publication `5b927f45-4286-40a0-bb20-0059958550a6`; verification artifact `1edce57a-890d-4f7a-965b-56ab37828a41`). `Geometry.lean`, `Statement.lean`, both linear modules, all prior verification files, the authoritative manuscript and dependency pins are preserved. The accepted statement receipt companion `dcd522c772885851078216fedcff18e00c3b1b7d` and supplemental complete type artifact `9b6e4713-9f54-47b8-9dfe-a233743bc854` remain applicable evidence; this additive branch does not replace their records or assert that the older truncated type log is complete.

## Definition crosswalk

| Manuscript object | Lean meaning |
| --- | --- |
| Fixed radial reference | The unchanged `RadialReference M`, with actual native manifold/forms, reference exact structure, smooth compatible `J`, smooth Riemannian `g`, proper smooth `R ≥ 1`, positive `c`, `rstar > 1`, and exterior radial identity/bound. |
| Positive smooth `rho` on `[1,infinity)` | `RadialCoefficient.rho : ℝ → ℝ` with `ContDiffOn ℝ ∞ rho (Set.Ici 1)` and positivity restricted to that set. Values below 1 are irrelevant. There is no global smooth extension assumption. |
| Constant on the core interval | `constant_core : ∀ r ∈ Icc 1 rstar, rho r = rho 1`. No radial identity for beta is assumed on the core. |
| `rho_prime` | `rhoPrime r := derivWithin rho (Ici 1) r`, the actual native within derivative, including the lower endpoint. |
| Radial positivity | `rho r + r * derivWithin rho (Ici 1) r > 0` for every `r ≥ 1`. |
| Primitive and two-form | `primitive` is literally `LinearAlgebraChecks.radialPrimitive P rho`, namely `rho(R) • beta`; its two-form is the native `M.exteriorDerivative primitive`. |
| `h_rho` | `metricValue x v w := d(rho(R) beta)(v,Jw)`. `metricBilin` constructs its continuous bilinear map. `metric` constructs `Bundle.ContMDiffRiemannianMetric`; `compatible` constructs the unchanged accepted `CompatibleStructure` with the original `J` definitionally. |
| `a` and `D` | `radialA = c * (P.compatible.dualNorm x dR)^2`; `radialD = rho(R) + rhoPrime(R) * radialA`. |
| Dual norms | The unchanged accepted `CompatibleStructure.dualNorm`: continuous-linear operator norm on the metric tangent synonym. `P.compatible` supplies `g`; `q.compatible` supplies the constructed `h_rho`. No chart norm is substituted. |
| `beta` as a covector | `RadialReference.betaCovector` uses Mathlib `ContinuousAlternatingMap.ofSubsingletonLIE` and evaluates exactly as the native one-form. |

These are additive lemma definitions. They do not change the accepted target or its input interfaces, or package unproved conclusions as assumptions. The only new input structure, `RadialCoefficient`, contains precisely coefficient data and hypotheses. `exactStructure`, `metric` and `compatible` are constructions with proof terms, not input fields.

## Proof map

`RadialCoefficient.lean` proves the half-line derivative, smooth composition, smooth derivative composition, and native manifold chain rule. To prove `rhoPrime_eq_zero` on the entire closed core interval, restrict the half-line derivative to `Icc 1 rstar` and compare it with the derivative of a constant. `rstar > 1` gives unique differentiation on that closed interval, including both endpoints. Thus the compact-core boundary is covered, not discarded. Composition uses the range condition `P.lower_R` and within-set chain rules on the full manifold; it remains valid at `R=1`.

`RadialMetric.lean` reuses the proved native variable-scalar exterior-derivative rule. `exteriorDerivative_apply` is `d(rho(R) beta) = rho d beta + rho_prime dR wedge beta`, evaluated on two native tangent vectors. With `beta=-c dR composed J` and `J²=-id`, `metricValue_exterior` gives

`h(v,w) = rho*g(v,w) + c*rho_prime*(dR(v)*dR(w) + dR(Jv)*dR(Jw))`.

`metricValue_core` uses the proved vanishing derivative and gives `h=rho*g` without using an exterior radial identity. `metricValue_eq` combines the cases into the same global formula, since its correction vanishes on the core.

`RadialMetricLinear.lean` constructs `CompatibleStructure.metricJ` as a linear isometry in the reference metric. The actual inner product is the accepted `metricInnerProductSpace` on the same core as the accepted norm. A two-vector Bessel estimate is proved from Cauchy–Schwarz, with no division by either vector length. Riesz representation then gives the sharp bound

`dR(v)^2 + dR(Jv)^2 ≤ |dR|_g^2 * |v|_g^2`.

Multiplying by `c`, using `a ≤ R` outside the core, and splitting on the sign of `rho_prime` proves `metricValue_lower_of_nonpos`, `metricValue_le_of_nonpos`, and `metricValue_ge_of_nonneg`, all pointwise on the full manifold. `metricValue_pos` uses `rho>0` or `rho+R*rho_prime>0`. `exactStructure` derives nondegeneracy by testing a kernel vector against `Jv`; smoothness and closedness come from the native exterior derivative theorems. `radialD_pos` uses `0 ≤ a ≤ R` and the same sign split.

`RadialMetricBundle.lean` proves native smooth covector/tensor bundle bridges. The differential is smooth by Mathlib `ContMDiffAt.mfderiv_const`; covector composition uses the existing smooth endomorphism section and genuine tangent trivialization cancellation. Covector squares are smooth bilinear sections via `smulRight`. Coordinates are used only to verify smoothness of native sections, never to measure a tangent or dual norm.

`RadialMetricConstruction.lean` constructs the native metric bilinear map by the proved global formula. Native smooth section addition/scaling and the preceding bridges prove its smoothness. A positive lower bound by a scalar multiple of the reference metric bounds its unit ball in the original tangent topology: scale vectors by the square root of that scalar and use the reference metric bounded-unit-ball field. This proves the native metric constructor requirement rather than adding it as input. Symmetry follows from the formula; positivity was already proved. Alternation and symmetry give invariance under the same `J`. Thus `compatible` has no new smoothness, invariance, positivity, or nondegeneracy assumptions.

`RadialMetricDual.lean` constructs `radialGradient` by the reference-metric Riesz equivalence and proves its pairing and norm. The exterior radial identity identifies the metric beta covector with `c` times the Riesz dual of `J grad R`, giving `beta_dualNorm` and `beta_dualNorm_sq`.

`RadialMetricNorm.lean` proves `metric_gradient_pair`: `h(grad_g R,v) = D*dR(v)`. Therefore `D^-1 grad_g R` is the Riesz representative of `dR` in the constructed `h`. Its squared norm is its pairing with `dR`, which is `|dR|_g^2/D = a/(c*D)`. Only `c` and `D` are inverted, and both are proved positive. The proof includes `dR=0` with no separate nonzero-gradient assumption. `dual_identities` collects all three manuscript dual assertions.

`RadialMetricChecks.lean` passes the constructed `exactStructure` and `compatible` directly to the delivered `LinearAlgebraChecks.first_path_linear_estimate`, using definitional primitive and `J` equalities. `decreasing_first_path` includes the full pointwise `m*g ≤ h ≤ rho*g` estimate under a generic nonpositive derivative assumption. It has no dependency on the small-coefficient construction, and makes no smoothness or flow claim about the pointwise solutions.

## Reuse audit, in required order

1. Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`: inspected and directly used `Analysis/Calculus/ContDiff/Deriv` (`ContDiffOn.derivWithin`), `Analysis/Calculus/Deriv/Basic` (`HasDerivWithinAt.derivWithin`), unique differentiation on closed intervals/half-lines, `Geometry/Manifold/MFDeriv/FDeriv` (`HasFDerivWithinAt.hasMFDerivWithinAt`), `HasMFDerivWithinAt.comp`, `ContDiffWithinAt.comp_contMDiffWithinAt`, `ContMDiffAt.mfderiv_const`, and native bundle section/trivialization rules. `Analysis/InnerProductSpace/Basic`, `LinearMap`, and `Dual` supply Cauchy–Schwarz, `LinearMap.isometryOfInner`, and `InnerProductSpace.toDual`. `Geometry/Manifold/VectorBundle/Riemannian` supplies the actual metric constructor; `Topology/VectorBundle/Hom` supplies `inCoordinates_apply_eq₂`; `ContMDiffSection` supplies smooth section addition and scaling. The pinned Mathlib exterior-derivative file has constant-scalar rules, but the intrinsic variable-scalar one-form rule is supplied by FsFltz.
2. FsFltz pin `1a3d387cfacc746e25aad31e5b27b1803103e7cb`: inspected `Smooth`, `SmoothForms`, `FormScalarDerivative`, `ExteriorDerivative`, and `BoundaryContactDistribution`. Reused `IsSmoothForm.function_smul`, `evalTwo_exteriorDerivative_smul`, `isSymplecticOn_exteriorDerivative_iff`, `evalTwo_smul_right`, and `evalTwo_swap`. The scalar product rule is proved from native Frechet product/chain rules in charts; it is not an assumed geometry operation. Positive contraction is in the first form slot. No FsFltz complete-Liouville or flow object is constructed here.
3. Exact cluster-skeleton source `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`, read-only operator archive with accepted provenance in `verification/cluster-access.json`: searched the actual source for radial metrics, Riemannian/dual-norm constructions, and variable-scalar differentiation. Its radial cutoff/dynamics lemmas are for its specialized torus/seed model, not this arbitrary compatible reference. The native covector conversion used in `TorusLiouvilleDynamics.native_equation_exists` agrees with the Mathlib equivalence already used by the accepted project. No suitable general radial metric/dual identity theorem was found; no old-project source is imported or edited.
4. New infrastructure is limited to the closed-half-line bridges, two-plane estimate, native smooth covector/tensor bridges, and the radial construction/proofs above. Existing metric and symplectic definitions are reused unchanged.

## Validation and ownership

Run `python scripts/verify-radial-metric.py`. The script uses managed checks under Horizon, verifies source and dependency identity, compiles the full radial consumer, audits every listed new declaration transitively, records bounded complete types, and rejects incomplete output or any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. `verification/radial-metric/receipt.json` records the source bytes; the verified private publication receipt binds the new files to their delivered commit.

Mission `b52749be-7471-4774-92ed-7c623614bbee` retains this bounded delivery and concrete review repairs. Root mission `040e593e-7a38-4959-9158-1caffe4e49fa` retains full-proof incorporation and recovery through its existing scheduler-owned planner. This delivery does not accept the full mission or phase, alter the graph, publish to GitHub, or produce final PDFs.
