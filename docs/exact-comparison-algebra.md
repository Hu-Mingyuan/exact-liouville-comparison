# Exact comparison algebra: bounded statement and crosswalk

Mission 41e09718-0654-46a2-a637-4f5c1dbf5528, revision 1. Base
f8b5b6bcb56a18c0094d15fed4619ff100327e30. This module supplies structural
laws from supplied comparison witnesses. It does not prove MainTarget, Cartan
exactness, Moser evolution, or the unconditional common-reference corollary.
`Geometry.lean` and all earlier semantic modules remain unchanged.

## Statement gate (before substantive proof)

`ExactComparisonAlgebraStatement.lean` defines five named specifications and
`Witness`, the conjunction of the existing ExactComparison witness conditions.
These are Prop definitions, not proved existence assertions. The implementation
must prove every specification and the corresponding reflexive, symmetric and
transitive laws for the unchanged `ExactComparison`.

For F*source = middle + dh and G*middle = target + dk, the witness is
F ∘ G, gauge k + h ∘ G. Native `G.trans F` means exactly F ∘ G.
Inversion uses F⁻¹ and −h ∘ F⁻¹. Identity uses id and zero.
Two supplied witnesses Fᵢ*sourceᵢ = reference + dhᵢ give
Phi = F₁ ∘ F₂⁻¹ (`F₂.symm.trans F₁`) and
q = (h₁ − h₂) ∘ F₂⁻¹. Every witness includes both the primitive evaluation
identity and the equality of pulled-back exterior derivatives.

## Definition crosswalk and ordered source inspection

1. **Pinned Mathlib first** (`d13f23b723b8a846827a245b89c10fc7d3f11612`).
   `Geometry/Manifold/Diffeomorph.lean`: `Diffeomorph.refl`, `.symm`, `.trans`,
   `.coe_trans`, `.apply_symm_apply`, `.symm_apply_apply`, `.symm_trans'`.
   These are actual smooth equivalences; trans applies its first argument first.
   `.contMDiff` gives smoothness and `.mdifferentiable` requires order ≠ 0.
   `MFDeriv/Basic.lean`: `mfderiv_comp` requires differentiability of both maps
   at the applicable points. `MFDeriv/SpecificFunctions.lean` supplies
   `mfderiv_add`, `mfderiv_sub` (differentiability of both inputs), `mfderiv_neg`
   and `mfderiv_const`. `ContMDiff/Basic.lean`: `ContMDiffOn.comp` requires
   the inner map to carry the source set into the outer smoothness set.
   `ContMDiff/Constructions.lean`: `ContMDiffOn.prodMk` and smooth projections
   give the parameter-preserving maps (t,x) ↦ (t,H_t(x)).
2. **Pinned FsFltz second** (`1a3d387cfacc746e25aad31e5b27b1803103e7cb`).
   `Smooth.lean`: SmoothManifold is an arbitrary finite-dimensional Hausdorff,
   second-countable native smooth real manifold without boundary; `Tangent`
   is native TangentSpace, `Form k` is a section of continuous alternating maps.
   `SmoothEquiv` is literally native Diffeomorph, not an abstract action.
   `pullback` (line 85) composes the alternating map with literal mfderiv;
   `scalarDerivative` (line 103) evaluates literal mfderiv into ℝ.
   `FormCalculus.lean`: `pullback_comp` has global MDifferentiable hypotheses
   and no regularity premise on the form; `pullback_id` and
   `pullback_symm_pullback` already prove identity and inverse cancellation.
   These bridges are reused directly.
   `ExteriorDerivative.lean`: `exteriorDerivative_pullback` requires a bundled
   SmoothMap and IsSmoothForm. It confirms naturality of the actual chartwise
   extDeriv. The bounded laws can transport the *supplied* exterior-derivative
   equality directly using pullback composition/cancellation, so they require
   no extra smoothness premise on source forms and do not need to reprove d²=0.
3. **Prior cluster-skeleton third**, unchanged archive at commit
   `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`.
   Full `GlobalSymplectic.lean` and `GeometryTarget.lean` inspected; archive-wide
   Lean search for exact comparisons, isotopies, pullback composition and scalar
   derivatives completed. `GlobalSymplectic.isSymplecticOn_omega` is specialized
   to the seed manifold and its global two-form. `GeometryTarget.LiouvilleData`
   carries the actual complete flow and positive contraction; its conversion
   preserves those data but does not establish comparison algebra.
   `GlobalLiouvilleField.contMDiffOn_scalarDerivative` proves smooth evaluation
   along a smooth vector field on an open set. `NormalizedPartnerNormDrift`'s
   `scalarDerivative_normSq` is a complex norm-square chain rule. Their full
   relevant proofs were inspected: neither supplies the needed real gauge
   sum/composition or smooth isotopy laws. No old source is changed or imported.

Minimal new bridges are scalar differentiation of composed real gauges and
of their sums/negatives, and pullback evaluation at a tangent vector. They are proved from these literal definitions and native chain rules as
`ExactComparisonAlgebra.evalOne_pullback`, `scalarDerivative_comp`,
`scalarDerivative_add`, and `scalarDerivative_neg`.

## Scope and isotopies

`SmoothlyIsotopicToIdentity` is used unchanged. Both directions must satisfy
ContMDiffOn on Icc 0 1 × univ. Identity uses a constant identity family;
inversion swaps forward and inverse families; composition uses the pointwise
family H_t ∘ K_t, with inverse K_t⁻¹ ∘ H_t⁻¹. This produces a smooth isotopy
without concatenating intervals, preserves endpoints, and needs no uniform
compact support. It proves precisely the manuscript's required identity-isotopy
conclusion (not the stronger time-dependent primitive-path assertion).

No metric estimate occurs in this algebra: g, dual norms and operator norms
remain the explicit unchanged definitions in Geometry.lean and are not inputs
to these structural laws. No object is newly called a Liouville manifold;
no completeness assertion or flow is inferred from a gauge change.

## Proved API and proof correspondence

Import `ExactLiouvilleComparison.ExactComparisonAlgebra` explicitly. The existing
root import and semantic modules are preserved. The API is:

| Declarations | Result |
| --- | --- |
| `SmoothlyIsotopicToIdentity.refl`, `.symm`, `.trans` | Native identity, inverse, and composition isotopies; `.trans` follows native diffeomorphism order |
| `ExactComparisonAlgebra.exactComparison_iff_exists_witness` | Proved equivalence between the unchanged relation and the explicit witness predicate |
| `ExactComparisonAlgebra.Witness.refl`, `.symm`, `.comp` | Explicit map and gauge witnesses with both identities |
| `ExactComparisonAlgebra.Witness.commonReference` | Literal `F₂.symm.trans F₁` and `(h₁-h₂) ∘ F₂.symm` |
| `ExactComparison.refl`, `.symm`, `.trans`, `.commonReference` | Structural laws for the unchanged existential relation |
| `ExactComparisonAlgebra.identity`, `.inversion`, `.composition`, `.commonReference`, `.isotopyLaws` | Proof terms inhabiting all five reviewed specifications |

`Witness.comp` pulls the first primitive equation back by G, substitutes the
second equation, and applies the native scalar chain and addition rules. Its
exterior-derivative equality uses the pinned pullback composition theorem.
`Witness.symm` evaluates the pinned inverse-pullback cancellation identity and
solves the resulting scalar equality, producing the negative composed gauge.
Its exterior-derivative equality uses the same cancellation theorem.
`Witness.commonReference` composes the first witness with the inverse second
witness and proves equality of the resulting gauge with the displayed difference.
No primitive smoothness, symplecticity, completeness or metric estimates are
added to these structural statements.

The isotopy proof uses an actual family of native diffeomorphisms. For native
`F.trans G`, it chooses `(H t).trans (K t)`; the forward joint map is K_t(H_t x)
and the inverse joint map is H_t⁻¹(K_t⁻¹ x). Both compositions preserve the time
coordinate and hence the closed domain `[0,1] × M`. Endpoints are proved
pointwise. Inversion swaps the two supplied smooth families.

`verification/exact-comparison-algebra/Consumers.lean` exposes composition and
inversion signs as literal function formulas, checks zero-gauge cancellation
for a comparison followed by its inverse, and supplies common-reference map,
gauge, primitive and exterior-derivative witnesses. A separate consumer expands
both isotopy directions on the closed interval. These consumers require already
proved comparison witnesses; none constructs the original radial comparisons.

## Verification and delivery boundary

Run `python scripts/verify-exact-comparison-algebra.py` from the repository root.
It uses `horizon-lean-check` when the managed policy is present, checks all source
pins and preserved semantic hashes, builds the bounded library, elaborates the
consumer and type inventories, and checks the transitive axiom reports against
exactly `propext`, `Classical.choice`, and `Quot.sound`. Output is staged outside
the checkout until the checks finish, preserving stable source snapshots.

The pre-proof exact-source statement receipt is `statement-check.json` and its
independent acceptance is `statement-review.md` in the verification directory.
The original native reviewer was interrupted without findings; its collected
recovery reviewer accepted the unchanged specifications before substantive proof.
`declarations.json` lists every new library definition and theorem; `Types.txt`
and `InterfaceTypes.txt` record elaborated types and native definitions.
`Axioms.txt`, `Consumers.txt`, and `receipt.json` record the bounded checks.
The independent final source review and exact private delivery binding are
recorded separately in that directory.

This child delivers only the structural algebra. Root mission
91f6a7c7-1eb9-4e2c-bb7e-39389d62ea18 retains Cartan exactness, application to
constructed Moser endpoints, main comparison, corollaries and final acceptance.
Third-path owner 715bfb6e-da34-4a2a-b10b-1821801f6a8a and scalar owner
abae5805-d5d0-4b35-901b-7721c33328fb are unchanged. No GitHub publication or
final PDFs are part of this delivery.
