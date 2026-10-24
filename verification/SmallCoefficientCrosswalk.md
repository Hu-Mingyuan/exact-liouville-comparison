# Small radial coefficient: scalar crosswalk and reuse

Scope: manuscript equations S, k, kproperties, m, kasymptotic and the scalar proper-growth limits. No radial metric, Moser evolution, large coefficient, comparison theorem or phase acceptance is claimed.

The accepted semantic base is 46fccea69cb9524882bbeda83b0ac2067d22a149, independently accepted in artifact 8930b2e3-ab88-498e-8a6f-d3f732fa8f95. The source base for this addition is its companion dcd522c772885851078216fedcff18e00c3b1b7d (verified publication 800654a4-db11-47a6-8266-295e42d4cc67). Exact repository-file API reads verified identical Geometry.lean, Statement.lean, aggregate import, manuscript, objective, definition crosswalk and dependency pins in the isolated build copy. These accepted files are unchanged. This addition does not redefine the accepted manifold, metric, growth witness or target.

All names below are in ExactLiouvilleComparison.SmallCoefficient.

| Manuscript | Actual definition/proof |
| --- | --- |
| Arbitrary admissible B | G : AdmissibleGrowth 1, directly imported from Statement. Its ContDiffOn on Ici 1 and Tendsto of interval integrals are used without strengthening. |
| S' = r/B(r)^2 | density; S_hasDerivWithinAt and S_derivWithin hold for every r ≥ 1. S_hasDerivAt gives the ordinary derivative for r > 1. |
| S = 1 + integral | S is literally the interval integral. S_smooth, one_le_S, S_le_one_add_log, S_tendsto, S_monotone, S_one. |
| theta and chi | chi rstar r = Real.smoothTransition (r-rstar). At the pin, smoothTransition is expNegInvGlue x/(expNegInvGlue x+expNegInvGlue (1-x)); expNegInvGlue is 0 for x≤0 and exp(-1/x) otherwise. Thus this is the manuscript formula, not just a cutoff with similar bounds. chi_smooth, chi_nonneg, chi_le_one, chi_zero, chi_one prove its required properties. |
| k exponential integral | rate and k use actual intervalIntegral and Real.exp. k_formula proves correspondence with S' interpreted as derivWithin at 1. |
| k' | kprime is derivWithin (k G rstar) (Ici 1). kprime_eq proves the differential equation; kprime_eq_deriv proves agreement with ordinary deriv for r>1. k_hasDerivWithinAt includes r=1. No two-sided derivative of the arbitrary B below 1 is assumed. |
| kproperties | k_smooth, k_pos, k_le_one, k_eq_one, kprime_zero, kprime_nonpos, k_antitone. |
| m = k+rk' | m is this expression by definition. m_eq proves the displayed manuscript formula; m_pos proves strict positivity, including where chi=1. kprime_smooth and m_smooth are derived, not fields. |
| Tail constant b0 | b0 is exp(integral_1^(rstar+1) rate - logProfile(rstar+1)), with logProfile = log(S)/2-log(r). b0_pos, rate_integral_tail, exp_logProfile, k_tail, m_tail, exists_tail_constant prove the two exact identities for every r≥rstar+1. |
| Proper-growth limits | radius_mul_k_tendsto and log_S_tendsto are actual Tendsto atTop atTop. log_S_hasDerivWithinAt also gives the scalar differential identity used by the first path. |

Endpoint bridge: integral_hasDerivWithinAt_Ici constructs F(x)=f(max(a,x)) and proves F continuous from ContinuousOn f (Ici a). This extension is used only for the continuous FTC. Equality of integrals on the ray transfers HasDerivWithinAt to the original integral. contDiffOn_integral_Ici then uses uniqueDiffOn_Ici and contDiffOn_infty_iff_derivWithin to obtain smoothness from the ORIGINAL smooth integrand on the ray. The max extension is never asserted to be smooth.

Mandatory reuse order was followed:

1. Pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612: Analysis.SpecialFunctions.SmoothTransition supplies the actual cutoff. MeasureTheory.Integral.IntervalIntegral.FundThmCalculus supplies Continuous.integral_hasStrictDerivAt and intervalIntegral.integral_eq_sub_of_hasDerivAt. IntervalIntegral.Basic supplies integral_congr, integral_nonneg, integral_mono_on and integral_add_adjacent_intervals. Analysis.Calculus.ContDiff.Deriv supplies contDiffOn_infty_iff_derivWithin. Analysis.SpecialFunctions.Integrals.Basic supplies integral_one_div_of_pos. Analysis.Calculus.Deriv.MeanValue supplies monotoneOn_of_deriv_nonneg and antitoneOn_of_deriv_nonpos. Real.exp_half, Real.tendsto_sqrt_atTop, Real.tendsto_log_atTop and native filter limits supply the asymptotics.
2. Pinned FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb: Analysis/SmoothRoundingProfile.lean cutoff and Analysis/TailoringFamily.lean tailoringEta also wrap Mathlib smoothTransition. No extra scalar dependency is needed; the accepted Statement imports its geometric dependencies unchanged.
3. Cluster-skeleton 2c239b0c03922a1549f18ee3a45a8e0ca25bb28c: read-only local snapshot from verification/cluster-access.json. ClusterSkeleton/PrimitiveCutoffs.lean transitionPrimitive_hasDerivAt and transitionPrimitive_smooth use the continuous FTC and smooth-derivative characterization on the full line. DominanceCutoff.lean chi is another affine smoothTransition cutoff. Reuse the proof pattern directly with Mathlib; importing specialized cluster data is unnecessary. Its full-line primitive result does not discharge the closed-ray endpoint obligation.
4. Only then add the two small closed-ray bridges and manuscript-specific formulas. No alternative calculus, derivative operation or growth certificate is introduced.

Dedicated consumer: verification/SmallCoefficientConsumer.lean, construction, uses arbitrary G and rstar>1. from_growthAtInfinity extracts the same G, C and compact exception from the accepted geometric growth hypothesis. There is no substitution B(r)=r or global smooth extension assumption.

Only the three new SmallCoefficient*.lean library modules and dedicated consumer/audit/reuse/verification files are delivered. Root may add aggregate imports on integration. Final PDFs and GitHub upload remain out of scope.
