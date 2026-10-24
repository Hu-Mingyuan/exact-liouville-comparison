# Mathematical definitions and proof map

This guide identifies the native objects and exact hypotheses used by the completed formalization. Read the [theorem guide](target-theorem.md) and [theorem PDF](../target-theorem.pdf) alongside it.

The pinned versions are Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb`. The definitions below refer to these implementations.

## Native geometry and signs

| Manuscript object | Lean representation and meaning |
| --- | --- |
| Finite-dimensional smooth manifold without boundary | FsFltz.Geometry.SmoothManifold d, for arbitrary natural d. Point has native topology, T2Space, SecondCountableTopology, ChartedSpace (EuclideanSpace ℝ (Fin d)), and IsManifold at smooth order ∞. Empty and zero-dimensional cases are not excluded. |
| Tangent fiber | SmoothManifold.Tangent M x is literally Mathlib TangentSpace of that charted manifold. |
| Real k-form | SmoothManifold.Form M k is a dependent section of ContinuousAlternatingMap on Fin k tangent arguments. evalOne and evalTwo evaluate on actual tangent vectors. |
| Smooth form | IsSmoothForm demands ContDiffOn ℝ ∞ of the coefficients transported by the actual inverse chart differential, on every chart target. ∞ means C-infinity, not analytic top. |
| d | SmoothManifold.exteriorDerivative is Mathlib extDeriv of the local coefficient form, transported back by the actual chart differential. ExteriorDerivative.lean proves chart independence, smoothness, square-zero and pullback naturality. No differential operator is supplied by the user. |
| Exact symplectic structure | ExactSymplecticStructure contains a smooth primitive and IsSymplecticOn of its actual exterior derivative on univ. The latter means smooth, closed, and contraction-nondegenerate. Smoothness and closedness of dλ are redundant properties, justified by upstream isSmoothForm_exteriorDerivative and exteriorDerivative_exteriorDerivative; not extra geometric restrictions. |
| Compatible J | CompatibleStructure has actual continuous linear fiber endomorphisms, native smooth section of the tangent endomorphism bundle, J²=-id, Ω(Jv,Jw)=Ω(v,w), and a native ContMDiffRiemannianMetric with equality g(v,w)=Ω(v,Jw). The native metric records symmetry, bilinearity, positive definiteness, the fiber topology and smooth dependence of the metric appearing in the source. No completeness property is included. |
| Pullback | SmoothManifold.pullback uses the actual mfderiv of the supplied map. |
| Scalar dh | SmoothManifold.scalarDerivative h x v is the actual native mfderiv of h applied to v. The primitive identity is stated pointwise on every tangent vector, avoiding an arbitrary derivative operation. |
| Positive contraction | flatLinear eta x maps v to the covector w ↦ eta(v,w), not eta(w,v). inverseContraction_equation checks that sign. Liouville contraction uses dλ(Z,v)=λ(v); the negative Moser sign is not confused with this definition. |

SmoothEndomorphism is a short predicate using native ContMDiff on the native tangent Hom bundle (Bundle.TotalSpace). Its smooth bundle atlas handles chart changes; no independent chartwise smoothness framework is introduced.

## The metric and every norm

MetricTangent A x is a separate type synonym of the actual tangent fiber, with its algebraic vector-space structure retained and its NormedAddCommGroup constructed by Mathlib InnerProductSpace.Core.toNormedAddCommGroup from A.g.toRiemannianMetric.toCore x. It is not the default/chart Euclidean norm. The proved tangent_norm_eq gives |v|_g = sqrt(dβ(v,Jv)).

Dual A x is the native continuous linear dual of that g-normed fiber. covector transfers the same native covector to it by its algebraic linear map; finite-dimensional continuity is proved by Mathlib, not assumed. covector_apply checks unchanged values. dualNorm is the actual Mathlib operator norm into ℝ. In particular the radial hypothesis uses this norm of mfderiv R, not the norm of its coordinate coefficients.

flatLinear is the algebraic contraction map into the algebraic dual. flatLinear_injective follows from the actual Nondegenerate predicate. flatEquiv constructs its inverse by equal finite dimensions of the space and its dual. inverseContraction composes that inverse with the forgetful map from the g-continuous dual and then uses finite-dimensional continuity. inverseContraction_equation proves eta(inverseContraction l,w)=l(w). inverseNorm is the actual continuous-linear-map operator norm from g-dual to g. No inverse operation or estimate is a certificate input. This definition also handles dimension zero without a nonempty-unit-sphere convention.

## Quantifiers and analytic hypotheses

| Source | Code and audit |
| --- | --- |
| R:X→[1,∞), smooth proper | RadialReference.R is real-valued with lower_R at every point, ContMDiff at ∞, and native IsProperMap. Properness as a real map agrees with properness into the closed half-line. |
| c>0, r*>1 | Explicit real fields positive_c and one_lt_rstar. |
| β=-c dR∘J and c|dR|²≤R outside {R≤r*} | radial_identity and radial_bound quantify only over points satisfying rstar<R x. No condition is imposed on the core, which is compact by properness. |
| Smooth B on a closed half-line | AdmissibleGrowth lower uses a real function whose values below lower are ignored, ContDiffOn ℝ ∞ on Ici lower, positive and dominating at every point of that closed half-line. Within-set smoothness includes the endpoint; no behavior outside the half-line is required. |
| Divergent improper integral | Tendsto (b ↦ ∫ r in lower..b, r/(B r)^2) atTop atTop, with actual intervalIntegral. Positivity and smoothness on the half-line ensure ordinary integrability on each finite integration interval there. This is positive divergence, not nonintegrability alone. |
| Weak taming | WeaklyTames is ∀x v, 0≤dλ(v,Jv), including zero and all nonzero tangent vectors. Nondegeneracy is separate in ExactSymplecticStructure. No strict inequality replaces it. |
| Inverse bound outside a compact subset | GrowthAtInfinity existentially quantifies admissible B, real C>0, and arbitrary compact K, then the pointwise bound only when x∉K. K is not required to coincide with the reference core. The B conditions are global on its half-line, even though the inverse estimate is only at infinity. |
| Unrestricted primitive growth | There is no bound on λ, λ-β, or their derivatives. |

MainTarget universally quantifies dimension, native manifold, radial reference and other exact symplectic primitive. No complete metric, complete primitive, local/global Moser flow, isotopy, or primitive exactness conclusion is an input.

## Conclusion and corollaries

ExactComparison M source target existentially quantifies an actual Mathlib Diffeomorph at order ∞, a smooth isotopy to identity, and a globally smooth real function. For every x and tangent v it requires F*source(v)=target(v)+dh(v), and also equality F*d(source)=d(target). Neither h nor the isotopy has a support restriction. No primitive-preserving InclusionMarking is used for this conclusion.

SmoothlyIsotopicToIdentity uses a family of actual diffeomorphisms, identity at 0 and F at 1. The family and inverse family are jointly ContMDiffOn on [0,1]×X. Values of the family outside [0,1] carry no joint smoothness requirement. Smoothness of inverses is part of the usual smooth-isotopy meaning, rather than a global flow hypothesis.

* thm:main ↔ MainTarget.
* cor:two ↔ CommonReferenceTarget. Both primitives have the same radial reference and independent existential C, B and compact K. Direction is Φ*λ₁=λ₂+dq. The symplectic equality is also included; it follows from the stated primitive identity and is not a strengthened mathematical demand.
* cor:liouville ↔ FiniteTypeTarget. The reference is FsFltz Completion of an actual compact LiouvilleDomain. Its ambient includes a complete all-real-time flow. CylindricalStructure uses the native endMap with logarithmic coordinate t, so manuscript r=exp t. The native end primitive is exp(t)α. The defining formula for J is the pushforward of (v,s)↦(Jξv+s Reeb,-α(v)); Jξ annihilates Reeb and maps to ker α. This encodes the r-independent compatible contact distribution structure and J(r∂r)=Reeb. Reeb satisfies α(Reeb)=1 and dα(Reeb,.)=0. The bound is only for t≥t₀≥0, using B(exp t). The radial exhaustion and its estimates are constructed in `FiniteTypeRadial.lean` and `FiniteTypeRadialMetric.lean`, then applied in `FiniteTypeComparison.lean`. The new primitive is exact symplectic, and need not be complete.
* cor:stein ↔ SteinTarget. ProperComplexEmbedding M N now starts from only the real native manifold, a smooth tangent complex structure J with J²=-id, and a smooth proper topological embedding and immersion into EuclideanSpace ℂ (Fin N). Its actual differential intertwines J with multiplication by i. It has no symplectic reference or metric input. This is the complex-submanifold presentation: the CR equation and immersion identify J with the induced complex structure. No independent integrability or symplecticity certificate is assumed.
* steinRadius is e+‖ι‖²=e+Σ|Fν|². SteinReference i is OUTPUT data in SteinTarget: an exact symplectic primitive, its compatible structure with exactly i.J, the identity β=-(1/4)dR∘J, and equality of g with the pullback of the real Euclidean inner product on ℂ^N. Thus both g=dβ(.,J.) and g(v,w)=Re⟨Dι(v),Dι(w)⟩ are explicit. These identities determine the reference independently of the comparison primitive. SteinTarget requires existence of this reference before universally quantifying the other primitive. It then uses the actual g dual/inverse norms, weak taming, compact exception, lower endpoint e and primitive conclusion. No finite type, completeness, radial estimate, properness of R or comparison flow is an input.

The Stein reference is constructed from the embedding by `SteinReferenceConstruction.reference` in [SteinReference.lean](../ExactLiouvilleComparison/SteinReference.lean). [SteinComparison.lean](../ExactLiouvilleComparison/SteinComparison.lean) proves `packagedSteinTarget` and the full `steinTarget`, choosing that reference before quantifying the target primitive. [ManuscriptComparison.lean](../ExactLiouvilleComparison/ManuscriptComparison.lean) combines all four comparison results.

[FiniteTypePresentation.lean](../ExactLiouvilleComparison/FiniteTypePresentation.lean) constructs the separate native presentation from an intrinsic Liouville domain. That adapter uses dimension `k + 1`; the cylindrical existence and extension theorems themselves retain every dimension allowed by their completion inputs. [NativeIntegration.lean](../ExactLiouvilleComparison/NativeIntegration.lean) constructs the cylindrical reference and performs comparison on that same native quotient.

## Complete Liouville terminology

The general theorem and its hypotheses are called exact symplectic. CompleteLiouvilleComparisonTarget separately takes CompletePrimitive witnesses for both actual primitives. At the pin this includes smoothness, symplecticity, smooth primitive-determined Liouville vector field, positive contraction, and CompleteLiouvilleFlow. The latter contains native Flow ℝ M.Point, a jointly smooth action, and the actual chart HasDerivAt equation for every x, every real t, and every chart containing the flowed point. Thus completeness is two-sided for all real times. It is neither a semigroup nor an arbitrary action. CompletePrimitive.toCompleteLiouvilleManifold preserves the same manifold, primitive, field and flow definitionally. No claim of Liouville-field conjugacy follows merely from +dh.

## Cylindrical existence and prescribed extension

The [cylindrical statement](../ExactLiouvilleComparison/CylindricalCompatibilityStatement.lean) distinguishes constructing some compatible contact data from extending specified data. For the latter, [extension_of_prescribed_kernel](../ExactLiouvilleComparison/CylindricalCompatibility.lean) starts with a smooth endomorphism j of the native kernel bundle, j squared equal to minus identity, preservation of the restricted d alpha, and strict positivity of d alpha(v,jv) for nonzero kernel vectors.

The output is a global compatible J that retains the prescribed end formula for every logarithmic coordinate t >= 0, including the seam. Its actual metric is d beta(.,J.). The auxiliary positive metric used in the extension argument is not substituted for this output metric. The [construction guide](cylindrical-compatibility-construction.md) explains the relative extension and recovery argument.

## Completed proof terms

Declaration names below are relative to `ExactLiouvilleComparison`.

| Statement | Proof term | Source |
| --- | --- | --- |
| General exact comparison | `MainComparison.mainTarget` | [MainComparison.lean](../ExactLiouvilleComparison/MainComparison.lean) |
| Finite-type comparison | `FiniteTypeComparison.finiteTypeTarget` | [FiniteTypeComparison.lean](../ExactLiouvilleComparison/FiniteTypeComparison.lean) |
| Stein reference and comparison | `SteinComparison.steinTarget` | [SteinComparison.lean](../ExactLiouvilleComparison/SteinComparison.lean) |
| Common reference | `CommonReferenceComparison.commonReferenceTarget` | [CommonReferenceComparison.lean](../ExactLiouvilleComparison/CommonReferenceComparison.lean) |
| Combined manuscript result | `ManuscriptComparison.manuscriptTarget` | [ManuscriptComparison.lean](../ExactLiouvilleComparison/ManuscriptComparison.lean) |
| Global cylindrical existence | `CylindricalCompatibility.existenceTarget` | [CylindricalCompatibility.lean](../ExactLiouvilleComparison/CylindricalCompatibility.lean) |
| Prescribed end extension | `CylindricalCompatibility.extensionTarget` | [CylindricalCompatibilityExtension.lean](../ExactLiouvilleComparison/CylindricalCompatibilityExtension.lean) |
| Native quotient construction and comparison | `NativeIntegration.constructedComparison` | [NativeIntegration.lean](../ExactLiouvilleComparison/NativeIntegration.lean) |

The [verification command](../verification/README.md) compiles these proof assemblies and checks the final theorem roots transitively against the allowed axioms `propext`, `Classical.choice`, and `Quot.sound`.
