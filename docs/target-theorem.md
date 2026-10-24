# Theorem and assumption guide

The project has two related conclusions: exact comparison relative to a specified radial reference, and construction or prescribed extension of a cylindrical compatible structure on a Liouville completion. The latter supplies reference data for the finite-type application. It does not remove weak taming or growth hypotheses from the target form.

## General exact comparison

The precise quantified statement is `MainTarget` in [Statement.lean](../ExactLiouvilleComparison/Statement.lean). Its proof is `MainComparison.mainTarget` in [MainComparison.lean](../ExactLiouvilleComparison/MainComparison.lean).

On a native finite-dimensional smooth manifold, the inputs are:

1. Smooth primitives beta and lambda whose actual exterior derivatives Omega and omega are symplectic.
2. A smooth Omega-compatible almost-complex structure J. Its Riemannian metric is the literal pairing `g(v,w) = Omega(v,Jw)`.
3. A smooth proper R with R >= 1, c > 0 and rstar > 1. On R > rstar, `beta = -c dR o J` and `c ||dR||_(g*)^2 <= R`.
4. Global weak taming: `omega(v,Jv) >= 0` for every tangent vector.
5. A smooth positive B on [1,infinity), with B(r) >= r and divergent integral of r/B(r)^2. For some C > 0 and compact K, the operator norm of `(omega-flat)^(-1)` from the g-dual norm to the g tangent norm is at most C B(R) outside K.

The output is an actual smooth diffeomorphism F, a smooth real function h, and a smooth identity isotopy with jointly smooth forward and inverse families, such that

$$F^*\lambda=\beta+dh,\qquad F^*d\lambda=d\beta.$$

The global weak inequality permits zero on nonzero vectors. The exceptional compact set applies to the inverse-form estimate. No growth condition on the primitive lambda, complete metric, or complete target Liouville field is added.

See [Geometry.lean](../ExactLiouvilleComparison/Geometry.lean) for the native form, derivative, metric, norm, diffeomorphism, and isotopy definitions; [definition-comparison.md](definition-comparison.md) gives their detailed crosswalk.

## Cylindrical existence and prescribed extension

The setting is a Liouville domain D with a completion C in the pinned FsFltz sense. Its end is parameterized by `(y,t)`, with `r = exp(t)` and primitive `beta = exp(t) alpha`. The completed reference has its prescribed complete Liouville data; the general exact-symplectic theorem above has different assumptions.

`CylindricalCompatibility.existenceTarget` constructs a smooth compatible J on the whole completion, cylindrical for every t >= 0. Existence of contact data is proved separately and then used here; it is not an input to this existence target.

For the prescribed-data version, start with a smooth compatible structure j on the actual contact bundle ker(alpha). Compatibility includes `j^2 = -id`, preservation of d alpha, and strict positivity of `d alpha(v,jv)` for nonzero kernel vectors. `extension_of_prescribed_kernel` constructs the global J while retaining exactly that j. If R_alpha is the normalized Reeb field and pi(v) = v - alpha(v) R_alpha, the end formula is

$$J_{\rm end}(v,s)=\bigl(j(\pi(v))+sR_\alpha,-\alpha(v)\bigr).$$

The differential of the actual end map transports this formula to the ambient tangent bundle. Equality holds for every t >= 0, including t = 0 (r = 1). The constructed structure satisfies square minus identity, symplectic compatibility, and the smooth positive-definite metric identity `g = d beta(.,J.)`.

The auxiliary positive metric used in the extension proof and the output metric are distinct objects. They agree as needed on the prescribed end; global equality between them is not assumed.

Contracts are in [CylindricalCompatibilityStatement.lean](../ExactLiouvilleComparison/CylindricalCompatibilityStatement.lean); proofs are in [CylindricalCompatibilityExtension.lean](../ExactLiouvilleComparison/CylindricalCompatibilityExtension.lean) and [CylindricalCompatibility.lean](../ExactLiouvilleComparison/CylindricalCompatibility.lean). The [construction guide](cylindrical-compatibility-construction.md) explains the native interfaces. The original dimensional scope, including the admissible empty and zero-rank cases, is retained.

## Applications and quantifier order

| Result | Input specific to the application | Proof |
| --- | --- | --- |
| Finite type with a specified cylindrical J | Actual completion C and compatible cylindrical A; target T weakly tames A and obeys the eventual end-growth bound | `FiniteTypeComparison.finiteTypeTarget` |
| Finite type with a constructed J | D and C first; a cylindrical A is chosen before quantifying T; the same target hypotheses remain | `CylindricalCompatibility.consumerTarget` |
| Stein reference | Proper smooth immersion/embedding with complex structure and the native Cauchy–Riemann equation; target weak taming and growth | `SteinComparison.steinTarget` |
| Common reference | Two targets, each weakly taming the reference J and each with its own B, C, K | `CommonReferenceComparison.commonReferenceTarget` |
| Complete specialization | Actual complete flows for the two prescribed primitives, in addition to the comparison hypotheses | `ManuscriptComparison.completeLiouvilleComparisonTarget` |

The finite-type estimate uses B(exp(t)) eventually along the end, and the proof constructs the global radial reference and compact exception. The Stein radius is `exp(1) + ||i(x)||^2`; its reference form and metric are constructed from the embedding data. The real Cauchy–Riemann input is stated explicitly rather than presented as a separately proved adapter from every possible holomorphic-embedding API.

The combined comparison proof is `ManuscriptComparison.manuscriptTarget`. [FiniteTypePresentation.lean](../ExactLiouvilleComparison/FiniteTypePresentation.lean) supplies the separate native presentation adapter. Neither an exact gauge change nor the comparison conclusion is used to infer completeness of a new primitive.

## Verification boundary

These descriptions identify the intended and implemented theorem terms. Source-bound receipts and independent reviews establish the scope of accepted results. The [verification guide](../verification/README.md) distinguishes those records from the pending combined publication check and PDF update.
