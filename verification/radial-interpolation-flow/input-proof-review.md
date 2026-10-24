# Independent bounded implementation review

Reviewer: delegated statement/proof reviewer, 2026-10-23. Parent confirmed the
three reviewed implementation sources stable before the hashes below were
recomputed. This review is independent source inspection, not a new Lean build
or a transitive axiom audit.

**Verdict: no mathematical or definition defect found in the reviewed bounded
implementation.** The native applicability proofs, coefficient specializations,
equal-coefficient existence result, and exterior critical-point result have the
advertised hypotheses and conclusions. The general radial interpolation
existence theorem is still open; the dependency adapter is not its proof.

## Source binding and evidence

| Reviewed file | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/RadialInterpolationFlowInputs.lean` | `9d90c3b0cf7bf4260edad41f785a07eca9a6bbe5dc6370fe5925fd212e4e54da` |
| `ExactLiouvilleComparison/RadialInterpolationFlowCoefficients.lean` | `c494e751fd75f7ad95a72e271ea4ca945c7ebfa947ff5c18a91459674a50806c` |
| `ExactLiouvilleComparison/RadialInterpolationFlowEqual.lean` | `97b2ba6eaafb09a8041726a295507cdab218f5424a12d8415bc84eb06c8a9462` |

The parent reports separate successful builds of Inputs and Equal, and the final
Coefficients build at source key
`4885fdd1ff649370f3acd20e9a58762e2e284343214ecb8a25fb547c9adc3e8b`.
That report includes the final `change`/`simp only [mul_one]`/`exact tendsto_id`
proof in `fourth_applicable`. These build results were not independently rerun;
the parent owns the final uniform-source-key build, type checks, and audit.

The prior statement review in `statement-review.md` covers the unchanged target,
crosswalk, native geometry, and full `Evolution` output. I additionally inspected
the actual producers in `FirstPathFlow.lean`, `FirstPathCoefficient.lean`,
`SmallCoefficientAsymptotic.lean`, `LargeCoefficient.lean`, and
`RadialInterpolationChecks.lean`, rather than relying on theorem names.

The three imported large-coefficient source hashes match
`verification/large-coefficient-review.json` exactly:

| Imported file | SHA-256 |
| --- | --- |
| `LargeCoefficient.lean` | `e07ab91f6341bcee9e67127424167c9689c9c24f96d8df2ba00ec03a197c0ff8` |
| `LargeCoefficientNorm.lean` | `fc1900c9fc9230508344d7e4c389c500ec4d5f2c6d74adaf1a96a950b6efbe46` |
| `LargeCoefficientSeries.lean` | `42d9e8a7113fedc34b77fc2fd55649d0e83a54d332ffb8eec5e50dcb277a3094` |

`FirstPathFlow.lean`, whose proved scalar-bound construction is used below, has
SHA-256 `d67f7c7692525f291deffbaf0df24ea478b59a243570ee4ccb7883ccfee35897`.
The parent identifies the imported large-coefficient delivery as commit
`1c07d33b09b9b45fc99714173d09d50c32c9c52e` and the unchanged first-path base as
`c8df2c59abe2fd72b241c5b2bffddbe422e93693`; this review verifies the local
source contents and listed hashes, not remote publication provenance.

## Proof findings

1. **Native barrier inputs.** `field_eq` is definitional equality with the
   already reviewed inverse contraction, preserving the Moser sign.
   `barrier_smooth` proves joint smoothness on all real time parameters by
   native composition and scalar operations. The existing `smooth_comp`
   theorem handles the closed radius endpoint without extending arbitrary
   coefficient values below 1. `barrier_time_derivative` uses the actual
   `HasDerivAt` theorem, and `barrier_time_nonneg` uses coefficient order and
   `R >= 1`, with no trajectory assumption. `barrier_sublevel` correctly uses
   uniform exhaustion at `L+1`, so its contradiction proves the non-strict
   sublevel implication without an equality gap.
2. **The analytic adapter discharges all input hypotheses.** `of_twoBarrier`
   obtains an actual open smooth extension from `interpolation_intervalSmooth`
   and `native_open_of_interval_family`. It supplies the original proper
   radius and the lower bound 1, the actual joint barrier, the uniform sublevel
   bound, and both constants from `interpolation_global`. It transports each
   rate estimate through exact interval agreement, including time 0 and 1,
   and rewrites the entire output evolution back to the literal field.
   The sole additional hypothesis is visibly `TwoBarrierEvolutionTarget`.
   The docstring correctly calls this a dependency adapter and explicitly
   leaves that analytic theorem unproved.
3. **Literal coefficient consumers.** `oneCoefficient` is the constant 1.
   `largeCoefficient` is the delivered `LargeCoefficient.A P lam`, without
   alteration or a substitute dominating function. Its core identity uses
   `A_core` both at the given radius and at 1. Radial positivity and
   `largeCoefficient_prime` transfer the ordinary derivative to
   `derivWithin` using `uniqueDiffOn_Ici`, which applies at radius 1 as well.
   Only smoothness of `lam` is added; no norm/growth/completeness condition
   is introduced. The imported construction of A uses the explicit reference
   dual norm and compact radial sublevels, as established in the prior review.
4. **Manuscript paths two and four.** `second_applicable` discharges order
   from `k_le_A`, divergence from the proved `radius_mul_k_tendsto`, and weak
   differential taming from the original `WeaklyTames` hypothesis.
   `FirstPath.coefficient.rho` is literally the delivered k. `second_rho`
   and `fourth_rho` identify the actual affine expressions, not merely
   pointwise bounds. `fourth_applicable` supplies the literal zero sigma
   case and divergence of the identity radius. This describes the forward
   path from beta to A beta; its inverse is the manuscript's fourth arrow.
   These are coefficient applicability results, not constructed flows for
   either unequal-coefficient path.
5. **Equal coefficients construct a genuine evolution.** `equal_evolution`
   proves the extended field is zero on the entire closed interval using
   the actual zero-delta contraction theorem, then proves an absolute scalar
   derivative bound of zero. It calls the existing proved
   `evolution_of_scalar_bound`, whose body constructs the smooth evolution
   and every required `Evolution` field. It does not assume that evolution
   or the two-barrier theorem. No divergence condition is needed in this
   zero-field case. The result is a valid special case under the given
   radial reference, not a replacement for the general target.
6. **Exterior critical points.** `critical_field_zero` retains
   `rstar < R x`. The underlying `critical_point` proof uses the radial
   primitive identity and vanishing native `mfderiv R` to force beta, hence
   the contraction covector, to vanish. Nondegeneracy of the interpolated
   form then gives zero field at every closed time parameter. It does not
   silently extend the radial identity to the compact core or assume
   nondegeneracy of d sigma. The theorem proves pointwise stationarity;
   a general trajectory-fixing statement remains a later flow consumer.

## Scope and outstanding acceptance

No reviewed module presents the conditional adapter or equal-coefficient case
as full mission acceptance. No admitted proof, custom axiom, or circular flow
field appears in these three sources. Final transitive axiom verification is
still required, including the imported scalar-bound construction used by Equal.

The general two-barrier theorem, its full native smooth evolution output, and
then unconditional radial interpolation flow consumers remain outstanding.
The parent assigns that analytic prerequisite to child mission `c88064ba` /
assignment `33e55321`. This review accepts the bounded source changes only;
it does not accept that child result, the radial interpolation mission, the
manuscript comparison theorem, or any final GitHub publication.
