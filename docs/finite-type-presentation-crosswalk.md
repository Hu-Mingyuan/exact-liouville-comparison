# Native finite-type presentation: bounded statement crosswalk

Mission 2cde2f71-9a68-4bf2-86cd-cfc13d8268cb. Status: statement submitted for independent pre-proof review. `NativeTarget` is a specification, not yet a proof. This closes only C1's promised source adapter; root retains combined acceptance and final packaging. The chosen cylindrical-J existence/extension belongs to sibling deee4e3c-9772-491a-b842-98913f062983.

## Source and unchanged interfaces

Authoritative manuscript: `docs/reference/exact_liouville_comparison.tex`, SHA-256 8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576, section “Two Liouville forms” and `cor:liouville`. Objective revision 1 and roadmap f8b5b6bcb56a18c0094d15fed4619ff100327e30 remain unchanged. The accepted private proof base is a2bc048aa4b718217b2dc414106ab4d5d14a3c70, publication 07d7653f-102f-4851-8ece-cd19ce87d968. Final coverage decision ae0f8bb3-2396-4e53-82c4-3e6fc4afdf77 explicitly permits the constructed-quotient route. No accepted geometry/comparison definition is modified.

The source compact manifold W is a native `M : Type`, with `TopologicalSpace`, `T2Space`, `SecondCountableTopology`, `CompactSpace`, `ChartedSpace (EuclideanHalfSpace (k+1))`, and `IsManifold (𝓡∂ (k+1)) ∞`. This bounded constructor covers positive dimensions k+1, exactly the pinned native construction. It does not assert a new zero-dimensional native construction; the accepted comparison theorem continues to quantify every dimension. Empty native manifolds are not excluded.

## Native smooth-boundary convention and source hypotheses

`IntrinsicLiouville.Form k M 1` is a section of continuous alternating maps on the actual Mathlib tangent fibers, including the full tangent space at boundary points. `IsLocallyExtendibleForm α` means that in every atlas chart the form coefficients admit smooth extensions to an open neighborhood in the ambient Euclidean model, agreeing as germs on the half-space chart target. This is the smooth-up-to-boundary convention here. No global extension manifold, extended field, collar, completion or complete flow is assumed. We do not claim a theorem equating this convention with a different within-set smoothness predicate.

The exterior derivative is the pinned intrinsic derivative defined from native within-chart exterior derivatives, with its coordinate law proved upstream. Nondegeneracy is pointwise triviality of the kernel of contraction. The native Liouville field is the inverse contraction of α by dα, not a freely supplied field. `IntrinsicLiouville.contraction_liouvilleVector` proves dα(Z,v)=α(v).

`LocalOutward α` is definitionally the exact last hypothesis of `IntrinsicLiouville.exists_completion_from_native`: at each native boundary point there is a local defining function ρ with ρ=0 at the point, ρ≤0 nearby in M, nonzero differential, a smooth ambient chart germ, and dρ(Z)>0. It does not require one global defining function, uniform collar data, or any global flow as input.

## Constructed quotient and identifications

`QuotientData α` packages OUTPUT witnesses from `IntrinsicLiouville.exists_liouvilleStructure_from_native`, the constructor used inside `exists_completion_from_native`. It retains that theorem's literal collar, positive width, smooth inverse germs, quotient Liouville structure, full native primitive pullback, cylinder formula, global nondegeneracy, canonical field equation, and native field equation. These laws are not premises of `NativeTarget`: the proof must construct every field from the native source hypotheses.

`P.domain` is the pinned `IntrinsicCompletionGluing.compactDomain` and `P.completed hα` is its pinned `completion`. `P.nativeIn` is literally `original` into the glued half-infinite quotient. This construction fixes the native boundary definitionally. The higher-level existential theorem hides that identification; retaining its existing lower-level witnesses avoids a redundant boundary transport theorem. No gluing or flow theory is reimplemented.

`P.Identifications hα` requests actual proof of: smooth closed embedding of M; bijective native derivative at every point; exact compact carrier and frontier; identity completion inclusion; pullback of the full original primitive on every tangent vector; preservation of the primitive-determined native field; literal original boundary inclusion; equality of the boundary form with `IntrinsicBoundary.restrictForm α`; equality of the flow end with the literal attached-cylinder map for t>−width (in particular every t≥0); and the all-real exponential boundary-end primitive formula. The all-real complete flow and end immersion/covering/overlap are already part of this actual constructed `Completion`. End embedding is required only at t≥0, not negative times. The manuscript coordinate is r=exp(t), so exp(t) times the original restricted primitive is exactly rα_boundary.

This is the constructed manuscript quotient, not a theorem identifying an independently supplied completion X. There is no claimed uniqueness, diffeomorphism to arbitrary X, or transport of X's primitive/J/metric. Such an API would require additional proved identifications and is outside this bounded route.

## Consumer, metric and quantifier order

`NativeTarget α hα` starts with only native nondegeneracy and local outwardness and produces `∃ P, P.Identifications hα ∧ P.ComparisonFor hα`. Thus P is fixed before the choice of compatible A/J, cylindrical data, or comparison primitive T. `ComparisonFor` retains exactly the accepted `CylindricalStructure` premise and weak taming `WeaklyTames A T`. T is exact symplectic and is not required to have a complete Liouville field.

`A.g` is the explicit native smooth Riemannian metric with A.metric_eq fixing g=dλ₀(.,J.). `A.dualNorm` is the dual norm of that metric on the actual tangent fiber; `A.inverseNorm T` is the operator norm of inverse contraction from the g-dual to g. The consumer keeps A literally, with no replacement metric or default chart norm. Its growth hypothesis is exactly the existential admissible B, C₀>0, t₀≥0 and bound at every end point with t≥t₀, using B(exp t). `AdmissibleGrowth 1` retains smoothness on the closed half-line, positivity, B(r)≥r and the divergent actual integral. No primitive-growth, radius, Moser-flow or new comparison assumption is added.

The output is the accepted `FiniteTypeComparison.NativeConclusion`: actual native diffeomorphism, smooth identity-start isotopy with smooth inverse family, globally smooth h, F*λ₁=λ₀+dh, and exterior-form equality. The proof will apply `FiniteTypeComparison.finiteTypeTarget` directly and its existing witness-unpacking theorem.

## Mandatory reuse inspection

1. Pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612: manifold boundary model (`EuclideanHalfSpace`, `𝓡∂`), `TangentSpace`, `mfderiv`, `ContMDiff`, continuous alternating forms, native flow and Riemannian metric structures are used literally through existing interfaces. Search of `Mathlib/Geometry/Manifold` for Completion/Liouville supplied no matching constructor; no new manifold/form infrastructure is introduced.
2. Pinned FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb: inspected actual `IntrinsicLiouvilleForms`, `IntrinsicLiouvilleCoefficients`, `IntrinsicCompletionLiouville`, `IntrinsicCompletionDomain`, `IntrinsicCompletion`, and `Liouville`. Reuse `exists_liouvilleStructure_from_native`, `completion`, native embedding/derivative/carrier/frontier lemmas, `boundaryForm_eq_restrictForm`, and `completion_original_end_primitive`. The top-level `exists_completion_from_native` is the inspected reference for source hypotheses and primitive/field preservation; its lower-level proof components preserve the additional boundary identification needed here.
3. Mandatory read-only cluster inspection at 2c239b0c03922a1549f18ee3a45a8e0ca25bb28c: `ClusterSkeleton/GeometryTarget.lean`, `LiouvilleData`, `toCompleteLiouvilleManifold`, and `field_eq_liouvilleVector`. These preserve actual full primitive/field/flow but specialize to the cluster presentation and provide no native compact-boundary adapter. Reuse the generic pinned completion construction instead.

No new foundational construction is needed. Compilation and independent review must precede substantive proof. Final validation must include this theorem's upstream completion closure, the existing comparison closure, exact source hashes and allowed-only transitive axioms (propext, Classical.choice, Quot.sound). No PDFs, final packaging or GitHub upload are in scope.
