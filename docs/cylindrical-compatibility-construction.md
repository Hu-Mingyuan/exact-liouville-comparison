# Cylindrical compatible structures and prescribed extension

The [statement](../ExactLiouvilleComparison/CylindricalCompatibilityStatement.lean) separates three results: extend specified contact data, construct some cylindrical compatible structure, and apply comparison using the constructed reference. The proofs are `extensionTarget`, `existenceTarget`, and `consumerTarget` in the namespace `ExactLiouvilleComparison.CylindricalCompatibility`.

[extension_of_prescribed_kernel](../ExactLiouvilleComparison/CylindricalCompatibility.lean) starts directly with a smooth endomorphism j of the native contact-kernel bundle, square minus identity, preservation of the restricted d alpha, and positivity of d alpha(v,jv) for nonzero kernel vectors. [FinalChecks.native_consumer](../ExactLiouvilleComparison/CylindricalCompatibilityFinalChecks.lean) obtains the diffeomorphism, smooth isotopy, and exact primitive identity from the constructed reference.

## Construction

Write R_alpha for the normalized Reeb field and pi(v) = v - alpha(v) R_alpha for the kernel projection. On the product end, define

$$J_{\rm end}(v,s)=\bigl(j(\pi(v))+sR_\alpha,-\alpha(v)\bigr).$$

The actual differential of the end map transports this operator to the open escaping basin. The proof establishes its native Hom-bundle smoothness and computes compatibility with the ambient d beta, including the exp(t) factor in beta = exp(t) alpha.

The entire image of t >= 0 is closed and lies in the open basin. Relative positive-metric extension fixes the induced pairing on this whole set, including t = 0. Smooth symplectic normalization then constructs a global compatible J. Its recovery theorem gives exactly the prescribed operator wherever the auxiliary metric agrees with the end metric. The output metric is constructed separately as the literal pairing d beta(.,J.); it is smooth and positive definite.

| Ingredient | Lean implementation |
| --- | --- |
| Native contact data and compatible kernel structure | [CylindricalCompatibilityContactExistence.lean](../ExactLiouvilleComparison/CylindricalCompatibilityContactExistence.lean) |
| End operator and transport | [CylindricalCompatibilityEndTransport.lean](../ExactLiouvilleComparison/CylindricalCompatibilityEndTransport.lean) |
| Ambient exterior-form identity | [CylindricalCompatibilityEndForm.lean](../ExactLiouvilleComparison/CylindricalCompatibilityEndForm.lean) |
| Relative positive-metric extension | [CylindricalCompatibilityRelativeMetric.lean](../ExactLiouvilleComparison/CylindricalCompatibilityRelativeMetric.lean) |
| Smooth normalization and exact recovery | [CylindricalCompatibilityNormalizationBundle.lean](../ExactLiouvilleComparison/CylindricalCompatibilityNormalizationBundle.lean) |
| Global prescribed extension | [CylindricalCompatibilityExtension.lean](../ExactLiouvilleComparison/CylindricalCompatibilityExtension.lean) |
| Existence and comparison application | [CylindricalCompatibility.lean](../ExactLiouvilleComparison/CylindricalCompatibility.lean) |

## Scope and application

The construction retains every dimension and empty case allowed by the completion structures. The contact geometry proves the applicable low-dimensional boundary emptiness internally. The end, relative metric, and normalization constructions require no additional nonemptiness, positive-rank, parity, or dimension hypothesis. Native consumers include dimension zero and an empty boundary.

The compatible reference A is chosen before the arbitrary exact symplectic target T. Comparison still assumes global weak taming and the original admissible growth function and eventual inverse-form bound for T. There is no primitive-growth or completeness assumption on T. [NativeIntegration.lean](../ExactLiouvilleComparison/NativeIntegration.lean) uses the construction and the native presentation adapter on the same quotient.

The [verification guide](../verification/README.md) gives the reproducible library, consumer, and transitive axiom checks. The [proof PDF](../proof-blueprint.pdf) develops the mathematical argument.
