# Proof blueprint and Lean map

Read the [theorem guide](target-theorem.md) first. The [proof PDF](../proof-blueprint.pdf) develops the comparison argument and the cylindrical construction. The maps below identify their Lean implementations.

## Exact comparison

The comparison proof constructs four controlled deformation paths, proves their forward and reverse continuation, derives exact pullback identities using Cartan's formula with a smooth integral gauge, and composes the endpoint equivalences in the required order. It constructs the maps and gauges rather than assuming a global Moser flow.

| Step | Lean implementation | Mathematical role |
| --- | --- | --- |
| Native geometry and quantitative hypotheses | [Geometry.lean](../ExactLiouvilleComparison/Geometry.lean), [Statement.lean](../ExactLiouvilleComparison/Statement.lean) | Actual forms and pullbacks; the reference metric and its dual/operator norms; radial and growth data |
| Controlled interpolation and continuation | [RadialInterpolationFlow.lean](../ExactLiouvilleComparison/RadialInterpolationFlow.lean), [ODETwoBarrier.lean](../ExactLiouvilleComparison/ODETwoBarrier.lean) | Forward and reverse flow existence from radial estimates and the divergent integral |
| Exactness and smooth integral gauge | [MoserRegularityGlobal.lean](../ExactLiouvilleComparison/MoserRegularityGlobal.lean), [MoserExactness.lean](../ExactLiouvilleComparison/MoserExactness.lean), [RemainingPathExactness.lean](../ExactLiouvilleComparison/RemainingPathExactness.lean) | Derive endpoint pullback identities with actual smooth gauge functions |
| Compose and invert the four paths | [MainComparison.lean](../ExactLiouvilleComparison/MainComparison.lean) | Construct the final F, h, identity isotopy, and both primitive and two-form identities |
| Construct application references | [FiniteTypeRadialMetric.lean](../ExactLiouvilleComparison/FiniteTypeRadialMetric.lean), [SteinReference.lean](../ExactLiouvilleComparison/SteinReference.lean), [SteinComparison.lean](../ExactLiouvilleComparison/SteinComparison.lean) | Discharge radial and metric hypotheses in the finite-type and Stein cases |
| Assemble comparison results | [ManuscriptComparison.lean](../ExactLiouvilleComparison/ManuscriptComparison.lean) | Prove the original quantified manuscript targets |

The exact order is important. If G_i and H_i are the four forward endpoints and gauges, the proof first forms `Psi = G4^(-1) o G3^(-1) o G2 o G1`, with its gauge f obtained by the proved composition/inversion laws. It then takes `F = Psi^(-1)` and `h = -f o Psi^(-1)`. The definitions `psi`, `psiGauge`, `comparisonMap`, and `comparisonGauge` in [MainComparison.lean](../ExactLiouvilleComparison/MainComparison.lean) give these formulas explicitly; `comparisonWitness` proves their exact identity.

## Construct and extend cylindrical J

1. **Construct the contact geometry.** Build the actual smooth kernel bundle of alpha, its native metric and restricted nondegenerate alternating form, and the smooth normalized Reeb field. Normalization constructs a compatible kernel J. Restriction and zero-extension theorems preserve the actual native maps.
2. **Define the prescribed operator on the end.** For given compatible kernel data j, define the product operator `(v,s) -> (j(pi(v)) + s R_alpha, -alpha(v))`. Transport it using the derivative of the end map, proving native smoothness on the open escaping basin.
3. **Identify the induced positive metric.** Compute the ambient exterior form, including the exp(t) factor, and prove compatibility and smoothness of `d beta(.,J_end.)`. The closed end t >= 0 lies inside the open basin, so it includes the seam.
4. **Extend a positive metric relatively.** The relative-metric theorem extends the prescribed positive metric to the whole manifold, fixing it at every point of the closed end. It constructs its local background data internally.
5. **Normalize and recover the prescribed data.** Apply the proved smooth symplectic normalization to the extended metric. The recovery theorem gives the original J_end wherever the auxiliary metric agrees. Construct the output metric separately as `d beta(.,J.)`.
6. **Discharge existence and apply comparison.** Supply the independently constructed contact data to get some cylindrical J. For the prescribed variant, keep the user's j throughout. Choose the reference before quantifying the target primitive, then apply the comparison theorem with its unchanged weak taming and growth hypotheses.

| Ingredient | File |
| --- | --- |
| Native kernel bundle | [CylindricalCompatibilityContactBundle.lean](../ExactLiouvilleComparison/CylindricalCompatibilityContactBundle.lean) |
| Contact data and smooth kernel bridges | [CylindricalCompatibilityContactExistence.lean](../ExactLiouvilleComparison/CylindricalCompatibilityContactExistence.lean) |
| Smooth normalization | [CylindricalCompatibilityNormalizationBundle.lean](../ExactLiouvilleComparison/CylindricalCompatibilityNormalizationBundle.lean) |
| Relative metric extension | [CylindricalCompatibilityRelativeMetric.lean](../ExactLiouvilleComparison/CylindricalCompatibilityRelativeMetric.lean) |
| Global prescribed extension | [CylindricalCompatibilityExtension.lean](../ExactLiouvilleComparison/CylindricalCompatibilityExtension.lean) |
| Existence and comparison application | [CylindricalCompatibility.lean](../ExactLiouvilleComparison/CylindricalCompatibility.lean) |

The [detailed cylindrical guide](cylindrical-compatibility-construction.md) records the exact normalization, metric, and contact prerequisites. In particular, the auxiliary extended metric is not silently substituted for the final reference metric in the comparison estimates.

## Definitions and proof evidence

The Lean kernel checks the proof terms against their quantified statements. The [definition guide](definition-comparison.md) identifies the hypotheses and native geometric objects. Reproducible builds, transitive axiom checks, exact source hashes, and the document-to-code comparison are described in the [verification guide](../verification/README.md).
