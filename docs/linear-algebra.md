# Weak-taming linear algebra

This bounded result proves manuscript `lem:linear`. It does not prove the comparison theorem, radial compatibility, smooth vector fields, or any Moser flow. The module imports the accepted `Geometry.lean` at `46fccea69cb9524882bbeda83b0ac2067d22a149`; that file and `Statement.lean` are unchanged. Independent statement/crosswalk acceptance is artifact `8930b2e3-ab88-498e-8a6f-d3f732fa8f95`. New proof validation is in `verification/linear-algebra/receipt.json`, with an explicit declaration list and transitive audits.

## Mathematics and proof correspondence

Let `omega` and `eta` be bilinear forms on a real inner product space and let `J` be linear. Assume the actual metric identity `inner v w = eta v (J w)`, left nondegeneracy of `omega`, and `omega v (J v) >= 0`. For every `t >= 0`, `omega + t eta` is left nondegenerate. If its positive contraction with `X` equals the positive contraction of `omega` with `W`, then `norm X <= norm W`.

`weak_taming_linear_nondegenerate` and `weak_taming_linear_contraction` prove this slightly more general bilinear result. Alternating forms on finite-dimensional real vector spaces with a J-compatible eta satisfy these exact hypotheses with the induced h inner product. Neither finite dimensionality nor alternation is needed in the inequality proof; finite dimension is used by the accepted native `flatEquiv` to construct inverse contractions. No stronger taming hypothesis, resolvent bound, invertibility of a path, or flow is assumed.

For `t = 0`, nondegeneracy supplies equality of the two vectors. For `t > 0`, a vector in the kernel gives `omega(v,Jv) + t norm(v)^2 = 0`, forcing `v = 0`. For contraction, define `B(v,w) = omega(v,Jw)` and test the equation at `J(X-W)`. The nonnegative quantity `B(X-W,X-W)` equals `-t inner X (X-W)`. Thus `norm(X)^2 <= inner X W <= norm(X) norm(W)`. `norm_le_of_weak_positive_equation` formalizes this argument. This avoids the manuscript's resolvent construction while retaining all of its hypotheses and conclusion, including identically zero taming diagonal.

All names above lie in `ExactLiouvilleComparison`. The native results lie in `ExactLiouvilleComparison.CompatibleStructure`:

- `metricInnerProductSpace` uses Mathlib `InnerProductSpace.ofCore` on the very same `A.metricCore x` that defines the accepted norm; it does not replace that norm.
- `metric_inner_eq` proves that this inner product is the actual form evaluation `d reference.primitive(v,Jw)`.
- `weak_taming_nondegenerate` and `weak_taming_contraction` instantiate the generic bilinear proofs using the accepted positive `flatLinear` and the actual tangent `J`.
- `inverseContraction_norm_le` applies the estimate to the two canonical inverse contractions using the accepted `inverseContraction_equation` on both sides.

The type synonym `A.MetricTangent x` has the same vectors as the native `M.Tangent x`, with A's metric norm. The generic proofs are explicitly specialized with `E := A.MetricTangent x`. No chart norm is silently substituted. Existing accepted source is unchanged; the new inner product instance's metric identity and the consumer's use of the existing `tangent_norm_eq` check compatibility.

## First-path consumer and remaining hypotheses

`LinearAlgebraChecks.lean` imports the accepted statement. `radialPrimitive P k` is literally the native one-form `fun x => k (P.R x) • P.exactStructure.primitive x`. The input `H` is an exact symplectic structure whose primitive equals this form. Its compatible structure `A` must have the same J as `P.compatible`. These are precisely the compatible-form hypotheses that the later radial metric result must discharge; this bounded mission does not construct H or A or assume a path flow.

`radial_metric_norm` proves

`norm v = sqrt (d(k(R) beta)(v, P.J v))`.

Thus A's metric is the first-path h, with no identification with P's original g. `firstPathCovector` is the actual `-k(R) beta`, converted by Mathlib's one-form/continuous-linear-map equivalence and the accepted covector transport. `firstPathCovector_apply` checks its sign and evaluation.

`first_path_linear_estimate` takes the original `WeaklyTames P.compatible T`, transports it through the J equality, proves nondegeneracy, and constructs actual pointwise X and W by inverse contraction. It proves both equations with right-hand side `-k(R) beta` and the h-norm estimate for every real `t >= 0`. `zero_parameter` checks the endpoint consumer explicitly. No smoothness, completeness, or flow is claimed for these pointwise solutions.

## Reuse search, in required order

1. Pinned Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`: inspected `Analysis/InnerProductSpace/Defs.lean` (`InnerProductSpace.ofCore`), `Analysis/InnerProductSpace/Basic.lean` (`inner_sub_right`, `real_inner_self_eq_norm_sq`, `real_inner_le_norm`), and `Analysis/Normed/Module/Alternating/Basic.lean` (`ContinuousAlternatingMap.ofSubsingletonLIE`). These directly supply the metric and Cauchy–Schwarz/one-form interfaces used here. Also inspected `LinearAlgebra/FiniteDimensional/Basic.lean` (`LinearMap.injective_iff_surjective`) and `Analysis/InnerProductSpace/Dual.lean` (`InnerProductSpace.toDual_symm_apply`). Searched the analysis tree for accretivity/resolvents: the spectral/Rayleigh results do not directly give this non-self-adjoint weak-taming estimate. The elementary difference-vector proof needs no new inverse infrastructure.
2. Pinned FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb`: inspected `Geometry/Smooth.lean`, `FixedAmbient.lean`, and `ExteriorDerivative.lean`, and searched for weak taming/accretivity/resolvents. `SmoothManifold.Form`, `Tangent`, `evalOne`, `evalTwo`, `Nondegenerate`, and `exteriorDerivative` are the native wrappers used by the accepted interfaces. `Nondegenerate` is exactly trivial left kernel; contraction evaluates the first slot positively. There is no directly reusable weak-taming contraction theorem in the searched source.
3. Cluster-skeleton `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`: read-only search of its exact operator-provided source archive, whose provenance is in the unchanged accepted `verification/cluster-access.json`, for weak taming/accretivity/resolvents/inner product interfaces. Inspected `ClusterSkeleton/TorusLiouvilleDynamics.lean:native_equation_exists`: it reuses `ContinuousAlternatingMap.ofSubsingletonLIE` and finite-dimensional injectivity/surjectivity for native positive contraction. Its seed-specific carrier and Euclidean norm are not imported. The general compatible-metric inverse construction already exists in accepted Geometry; reuse that directly. No matching weak-taming estimate was located.
4. New infrastructure is limited to the elementary bilinear proofs and the proved compatible-inner-product bridge. The consumer reuses the existing native inverse contraction and the same one-form equivalence seen in the cluster source. No upstream source, dependency pin, old project, or manuscript was edited.

## Verification and ownership

Run `python scripts/verify-linear-algebra.py`. Under Horizon this uses managed `horizon-lean-check`; otherwise it uses the pinned Lake toolchain. It checks the bounded module and consumer, audits all 14 new declarations transitively, and records complete bounded elaborated type output. It verifies the accepted geometry/statement/manuscript hashes, dependency Git revisions, and source bytes before and after checks. Logs are collected outside the checkout during checks and only installed afterward; output truncation or omitted types fail verification. The receipt describes source bytes, and the private publication receipt binds those files to the delivered commit.

Mission `e95dab02-b46e-483d-81a9-2736b181d654` retains lemma delivery, review repairs, and integration of this source. Root mission `040e593e-7a38-4959-9158-1caffe4e49fa` owns the remaining radial compatibility proof, full-theorem integration and recovery through its existing scheduler planner. The statement author owns the existing statement verification/C2 files. No full theorem, phase, final PDF, or GitHub publication is claimed.
