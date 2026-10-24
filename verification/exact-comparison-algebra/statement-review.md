# Independent bounded statement review

Verdict: **ACCEPT for substantive proof work on the five bounded structural laws.**
This is a source review of specifications and their definition crosswalk, not a
proof acceptance or acceptance of the main theorem. Reviewer:
`/root/statement_review_recovery`, independent of the statement author.
Review date: 2026-10-23. Statement/crosswalk commit supplied by the parent:
`475bcecf1dec65293b9fe7ba6e63f5a9730cd78d`. The hashes below identify the
actual files read; no build or implementation was performed in this review.

## Findings

1. `Witness` is exactly the conjunction under the existing existential
   witnesses in `Geometry.lean`'s `ExactComparison`: identity isotopy, global
   smoothness of the real gauge, the primitive identity evaluated on every
   native tangent vector, and the pulled-back exterior-derivative equality.
   It adds no assumed comparison existence or geometric operation. For a
   one-form, evaluation on every vector determines the alternating map, so
   the primitive equation has the intended meaning.
2. Direct inspection of pinned `Smooth.lean` confirms native manifold and
   tangent-space definitions, continuous alternating forms, native
   `Diffeomorph`, pullback through actual `mfderiv`, scalar differentiation
   through actual `mfderiv`, and exterior differentiation through chartwise
   `extDeriv`. `Diffeomorph.coe_trans` states that `G.trans F` is `F ∘ G`.
   These are actual geometric objects, not replacement abstract operations.
3. The gauge signs and map order are correct. From
   `F*source = middle + dh` and `G*middle = target + dk`, pullback composition
   gives `(F ∘ G)*source = target + d(k + h ∘ G)`. Pullback by `F⁻¹` gives
   `(F⁻¹)*target = source + d(-h ∘ F⁻¹)`. Identity uses the zero gauge.
   Combining the two common-reference witnesses gives precisely
   `F₁ ∘ F₂⁻¹` and `(h₁ - h₂) ∘ F₂⁻¹`, with the orientation
   `Phi*source₁ = source₂ + dq`. This agrees with the manuscript's
   exactness/inversion paragraph (lines 345–374) and common-reference proof
   (lines 451–465).
4. No regularity of source forms is silently required for these laws:
   `FormCalculus.pullback_comp`, `pullback_id`, and
   `pullback_symm_pullback` transport the *supplied* exterior-derivative
   equality directly. Their actual premises were inspected. By contrast,
   `ExteriorDerivative.exteriorDerivative_pullback` requires a smooth form;
   the crosswalk correctly distinguishes that theorem and does not apply it
   to arbitrary forms. The scalar chain-rule bridges remain proof obligations.
5. Both isotopy directions are present in the unchanged native definition:
   joint `ContMDiffOn` for `(t,x) ↦ H_t(x)` and `(t,x) ↦ H_t⁻¹(x)` on
   `[0,1] × M`. The identity family meets both conditions. Inversion swaps
   these two families. For composition, if `H` ends at `F` and `K` at `G`,
   use `L_t = H_t ∘ K_t`; its inverse is `K_t⁻¹ ∘ H_t⁻¹`. Each joint
   composition factors through a parameter-preserving map, which preserves
   `[0,1] × M`; the time-zero and time-one endpoints are identity and
   `F ∘ G`. Thus the specifications do not omit inverse-family smoothness,
   do not need interval concatenation, and preserve the intended isotopy
   conclusion. The common-reference map inherits these laws.
6. Scope is honest: these are `Prop` specifications conditional on supplied
   witnesses, not proofs of radial comparison, Cartan exactness, Moser-flow
   existence, or the unconditional common-reference corollary. No new object
   is called Liouville and no complete flow is inferred. Metric estimates
   play no role in this structural algebra. The explicit reference metric
   and dual/operator norm definitions in `Geometry.lean` are unchanged.
   The stronger manuscript assertion about a simultaneous primitive path is
   expressly outside this bounded statement; accepting this gate does not
   discharge that assertion.

The supplied exact-source compilation receipt reports `status: passed`,
`ok: true`, `returncode: 0`, and `snapshot_verified: true` for
`ExactLiouvilleComparison.ExactComparisonAlgebraStatement`. I inspected that
receipt and did not independently rerun compilation.

Documentation-only note: the crosswalk's final section still says
“Statement compilation and independent review pending.” Integration should
update that status to cite the passing receipt and this bounded review. This
does not change the accepted mathematical specifications. Historical claims
about inspection of the old cluster archive are outside this bounded review;
they are not needed for the acceptance verdict above.

## SHA256 source binding

| File | SHA256 |
| --- | --- |
| `ExactLiouvilleComparison/ExactComparisonAlgebraStatement.lean` | `c6059259870eefe1ac19c2b81694d669d884abb0f99ca38351701a09e97a3a36` |
| `docs/exact-comparison-algebra.md` | `f9a6e15d8cd57ead2946ceb3d39d0f74f4579fb4f3fc721c67586b4eaf9e261c` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `verification/exact-comparison-algebra/statement-check.json` | `687dc68d29fcfc5aaf9510dd12b1b36681c8b16a9122583c863150b52dd9bc18` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| `.lake/packages/fsfltz/FsFltz/Geometry/FormCalculus.lean` | `58cc166d746f720c205135fffbe494fd15d6486a2c78de2f860cd36e4828c96a` |
| `.lake/packages/fsfltz/FsFltz/Geometry/ExteriorDerivative.lean` | `498095c7bfa18204b0bb1bfba2943c42e3c257d27a74efe85e85df74077962ad` |
| `.lake/packages/mathlib/Mathlib/Geometry/Manifold/Diffeomorph.lean` | `077bc7d6ffed47ed4daf67615380238ffa4652bbfe7a5ccb7d9aa9e31bdc7be6` |
