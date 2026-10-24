# General radial comparison proof guide

Import `ExactLiouvilleComparison.MainComparison`. The theorem
`ExactLiouvilleComparison.MainComparison.mainTarget` inhabits the unchanged
`ExactLiouvilleComparison.MainTarget`. This bounded delivery proves the general
radial theorem. It does not establish the finite-type, Stein, common-reference
corollaries, full-objective acceptance, or final project packaging.

The independently reviewed statement is `MainComparisonStatement.lean`, with
crosswalk in `docs/main-comparison-crosswalk.md` and source hashes and review
under `verification/main-comparison`. All baseline and imported semantic files
remain unchanged. The authoritative manuscript and pinned dependencies are
untouched. No completeness of the primitives or metric, primitive growth bound,
extra flow, exactness, or integral regularity assumption has been introduced.

## Path applications

`RemainingPathExactness.lean` proves `interpolation_affine`: the all-real literal
interpolation primitive equals (σ+q0β)+t(q1β−q0β). The delivered native
`smoothFormFamily_affine` proves its family smoothness. The existing
`RadialInterpolation.primitive_parameter_derivative` differentiates the actual
coefficient, and `vector_equation` proves contraction with its negative.
`interpolation_equation` is their minimal equality bridge to the exact
`MoserExactness.Equation` interface. The existing interval-smooth field and the
constructed `RadialInterpolationFlow.evolution` discharge the remaining generic
premises. No new ODE or integral calculus is constructed.

`second_eq_interpolation` is literal equality for q0=k, q1=A, σ=λ.
`fourth_eq_interpolation` proves 1+v(A−1)=(1−v)·1+vA and σ=0.
The accepted coefficient applicability theorems discharge every order,
divergence and weak-differential premise. For the third path, the delivered
`ThirdPath.primitive_parameter_derivative`, `field_equation`,
`primitive_family`, `field_intervalSmooth` and `evolution` suffice directly.
`second_exactness`, `third_exactness`, and `fourth_exactness` give Cartan's
pullback derivative and endpoint equality with the literal integral gauge,
including its global smoothness and the exterior-derivative identity.
`remainingPaths` proves the unchanged bounded three-path target.

## Actual endpoint, gauge and isotopy

`MainComparison.lean` proves four endpoint equality bridges and repackages each
proved endpoint as `ExactComparisonAlgebra.Witness` with its actual evolution
isotopy. For the first path it uses the delivered unconditional
`FirstPathExactness.firstPathExactness` at the original B,C,K hypotheses.
Let Gi be the four constructed forward endpoints and Hi their literal gauges.
`psi` is G4⁻¹∘G3⁻¹∘G2∘G1. `psiGauge` is the exact expression produced by
composition and inversion:

f(x) = H1(x) + H2(G1(x)) − H3(G3⁻¹(G2(G1(x))))
       − H4(G4⁻¹(G3⁻¹(G2(G1(x))))).

`psiWitness` composes inverse fourth, inverse third, second and first witnesses
in exactly that order. `comparisonMap` is Ψ⁻¹ and `comparisonGauge` is −f∘Ψ⁻¹.
`comparisonWitness` applies the already proved inversion algebra. It proves
smooth identity isotopy with both forward/inverse families, global smoothness
of h, F*λ=β+dh and F*dλ=dβ, for these specified witnesses.
`exactComparison` forgets only their names. `mainTarget` destructures the
original `GrowthAtInfinity` existential and applies this result. All dimensions,
all admissible growth witnesses, weak taming and the compact exception persist.

The actual g tangent, g-dual and g-inverse operator norms remain those of the
unchanged Geometry module. Native geometry and all-real Liouville completeness
conventions are documented in the reviewed crosswalk. This general theorem
concerns exact symplectic structures and needs no Liouville completeness input.

## Reproduction and evidence

Run `python scripts/verify-main-comparison.py` from the project root with the
existing managed Lean environment and caches. It serializes the library build,
full relevant declaration/type/axiom inventory and native consumers. It verifies
all baseline bytes, imported source hashes, reviewed statement hashes, dependency
pins, source stability and exact managed snapshots. The environment inventory
includes generated declarations and the specific imported interfaces consumed
by this assembly. The imported components retain their original broader
inventories and accepted source-bound reviews.

`verification/main-comparison/Consumers.lean` inhabits MainTarget and the
remaining-path target, unfolds the advertised native conclusion, and consumes
the explicit inverse map and gauge. `Audit.lean` emits nonelided fully elaborated
types and a transitive axiom audit; only propext, Classical.choice, Quot.sound
are accepted. Exact receipts and type hashes are under `final/` after successful
verification. The final independent source-bound review and private publication
identify the delivered commit separately. No final PDFs or GitHub upload belong
to this bounded mission.
