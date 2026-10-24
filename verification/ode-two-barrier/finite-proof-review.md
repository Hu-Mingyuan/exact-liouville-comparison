# Independent source review: two-barrier finite interval existence

Reviewer: delegated independent reviewer, 2026-10-23. No implementation edits or Lean builds were performed.

**Verdict: pass for the finite interval existence component. No source-level defect found.** This does not establish `TwoBarrierEvolutionTarget`, the radial interpolation flow target, or the manuscript theorem. Smooth dependence, closed-interval uniqueness, the actual evolution/diffeomorphism/isotopy assembly, applicability consumers, and final integration acceptance remain outside this review.

The parent reports successful compilation under managed source key `822c3749a02cefa3bf74bf91946a55e1363f780103bfa7b3a863655402e65df2`. That is supplied compilation evidence, not an independently rerun build or a transitive axiom audit. The present review inspected the actual source bytes listed below.

## Findings

1. The immutable analytic statement and its reviewed crosswalk are preserved: the existence theorem takes precisely the target's native smoothness and scalar hypotheses, followed by an initial parameter and point. It adds no absolute rate bound, complete metric, supplied trajectory, assumed flow, or stronger smoothness domain. The statement and crosswalk hashes match their earlier statement review.
2. Cutoff stability has the correct signs. For `0 <= chi <= 1`, the forward rate is `chi * ZR <= C0` using `C0 >= 0`. The reverse total rate is `chi * (partial_t Q + ZQ) + (1-chi) * partial_t Q >= -C1`, using the stated nonnegative partial time rate and `C1 >= 0`. No derivative of chi belongs in either calculation: these are directional derivatives along the scaled field, not derivatives of the field itself. The cutoff is allowed to depend jointly on time and position.
3. `twoBarrier_hasDerivAt` is a genuine native chain rule. It differentiates `t -> (t, gamma t)` with `HasMFDerivAt`, composes with the jointly smooth Q, and applies Mathlib's actual `mfderiv_prod_eq_add_apply`. Its two terms are the ordinary real partial derivative at fixed spatial point and FsFltz's `scalarDerivative`, literally native `mfderiv` evaluated on the tangent vector. The spatial derivative lemma uses the same native chain rule. No arbitrary derivative operation is introduced.
4. The compact confinement set is chosen before both the cutoff and the trajectory. Uniform coercivity is invoked at `L = Q(s,x) + C1` to obtain A, then `K = {y | R(y) <= max (R(x)+C0) A}`. Properness and a lower bound on R prove this sublevel compact. The resulting statement quantifies all candidate fields and trajectories only after K. For `s <= t`, the mean value estimate gives the forward R bound; for `t <= s`, the lower total Q-rate gives the reverse upper Q bound, then coercivity bounds R. The two time differences are at most one. Equality and both parameter endpoints are included.
5. The cutoff producer constructs a native smooth function valued in `[0,1]`, equal to one on an open neighborhood of `[0,1] x K`, with compact support contained in the supplied open smoothness domain. The prior `contMDiff_cutoff_field` proof uses the native product tangent bundle equivalence and section multiplication to extend `chi Z` globally smoothly; it does not assume Z is globally smooth outside its domain.
6. The invoked pinned `CollarFlow.exists_global_solution` is a proved producer requiring a globally smooth field vanishing off a compact spacetime set. Its literal conclusion supplies a curve through the initial point with full `HasMFDerivAt` at every real time. Its source derives this from native local Picard-Lindelof integration, compact uniform local lifetime, time suspension, and Mathlib uniform-time continuation; an existing curve is not an input. The present proof discharges compact support by `tsupport chi` and vanishing outside that support.
7. The constructed auxiliary trajectory satisfies the cutoff-stable barriers, hence lies in K throughout the closed interval. Thus chi equals one at every trajectory point in the interval, and its full derivative equation simplifies to the original field's equation. In particular, t=0 and t=1 retain full `HasMFDerivAt`, not merely one-sided derivatives. The conclusion does not assert that the same curve solves the original field outside `[0,1]`, nor is that needed.
8. No `sorry`, `admit`, `sorryAx`, custom axiom, or opaque declaration occurs in the two new modules or the inspected cutoff, scalar-confinement, and FsFltz continuation modules. Source inspection is not a transitive axiom audit: the required exact-source audit of the resulting declarations remains an integration obligation. No complete Liouville structure is claimed here, and these abstract scalar arguments introduce no alternative metric or norm.

## Exact reviewed artifacts

Paths are relative to the scratch `two-barrier/` tree.

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/ODETwoBarrierConfinement.lean` | `bd10ac404e00c985b50091701882400f08576e77758ebd85eeffdbd419501959` |
| `ExactLiouvilleComparison/ODETwoBarrierExistence.lean` | `fc2efd63070a58bf63b84ce143cbc850dddd9aace5b4e93ca9d580a85507a8df` |
| `ExactLiouvilleComparison/ODETwoBarrierStatement.lean` | `81b206239999b41a479672cc5a73673115a5c09f3393d0438674bf2df794eb17` |
| `ExactLiouvilleComparison/ODEContinuationCutoff.lean` | `7371c5defeccd22af52bf034cd66aacb642d2181da2ef1d49e62cf5cccc4e80b` |
| `ExactLiouvilleComparison/ODEScalarConfinement.lean` | `0b07b6c8765cb2cbe1a81407ec1f051f80fd9d3f5003fe711a99e2c708083fa8` |
| `verification/radial-interpolation-flow/crosswalk.md` | `54ed4154d99265fbbbb29d6e63c2506fee66f59c7a1cca58d7f574068c87b732` |
| `verification/radial-interpolation-flow/statement-review.md` | `540e299db4d8835212bf708e1dcac3a0fc73e83229e55b0805ed521342e0f9eb` |
| `.lake/packages/fsfltz/FsFltz/Geometry/CollarEvolution.lean` | `162ec4959c8d51f82c8bb6c59dff9074a84abf98dde4978d256d1851c1eaa361` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| `.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean` | `2a30c718ae95da8318eca42b7bc27385b2b54630ee9b35111d1abdfd3bfebaef` |

I also read the objective and unchanged manuscript, and checked `Family.lean` for the literal `parameterInterval = Icc 0 1` and `Parameter = Set.Icc 0 1`. The inspected manifest retains FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. This bounded review does not independently audit every transitive imported proof or certify final mission acceptance.
