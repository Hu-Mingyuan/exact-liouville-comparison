# Independent final first-path flow proof review

Reviewer: delegated independent agent `final_flow_review`, 2026-10-23.

**Assessment: PASS for the bounded mathematical source review.** The reviewed
proofs construct the unchanged `FirstPathFlow.Target` and `GrowthTarget`, with
actual trajectories, native smooth diffeomorphisms, both time parameters and
endpoints, closed-interval uniqueness, chart ODE, evolution identities, and
identity-start smooth isotopy. No substantive mathematical defect, added input
hypothesis, assumed Moser flow, or circular construction was found.

This assessment is confined to first-path evolution. It does not establish
Cartan exactness, the other three paths, the comparison theorem, or its
corollaries. The previously reviewed radial estimates and first-path input
packages were used as inputs, not independently re-proved in this review.

## Exact reviewed source

Hashes were taken after the author confirmed the proof and consumer source
stable. The final endpoint-gluing elaboration changes and the warning-only
`ext r` to `ext` change in `ODEGlobalExistence` are included.

| Input | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/ODEGlobalField.lean` | `25a4cb46ce0bfa489b9ebfe4ba41f3fbbcbb34549befd8c7c6379044a9f91957` |
| `ExactLiouvilleComparison/ODEGlobalExistence.lean` | `3554dfd76cdefb2973d9a698d4e7d16e66f627e781befdf639409e2a739c4dfb` |
| `ExactLiouvilleComparison/ODESmoothEvolution.lean` | `6f70c38ccfe9628315b20fd8cfc313521529d708fbbc374020d3ebced26981f8` |
| `ExactLiouvilleComparison/ODEClosedUniqueness.lean` | `0a3fb154cb14c001e086402169e49af6fcdf78d2ae366c0a05b5584f8183fc33` |
| `ExactLiouvilleComparison/FirstPathFlow.lean` | `d67f7c7692525f291deffbaf0df24ea478b59a243570ee4ccb7883ccfee35897` |
| `ExactLiouvilleComparison/FirstPathFlowFinalChecks.lean` | `b89ec691fae1a9f2663fa08b03e03c5bde71b622d29f0301e804bf1a1063ed29` |
| `ExactLiouvilleComparison/FirstPathFlowStatement.lean` | `2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217` |
| `ExactLiouvilleComparison/ODEContinuationStatement.lean` | `d1f8ad17b89f7acea0a9c757319bcfc027666df264c9471ba01d0c03164598f1` |
| `ExactLiouvilleComparison/ODEContinuation.lean` | `23f47f09944ddff65928949fe7385226a2e7b3b274dda87396eec8b155de9927` |
| `ExactLiouvilleComparison/ODEContinuationCutoff.lean` | `7371c5defeccd22af52bf034cd66aacb642d2181da2ef1d49e62cf5cccc4e80b` |
| `docs/first-path-flow-final.md` | `44139afbe1acd0f6e539925fc13f7b7260f756a9afdd11eec7b089158aa8b4b0` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |

The statement and manuscript hashes agree with the previous independent
statement review. That review and the earlier crosswalk and prerequisite proof
review were read before inspecting the new constructions.

Actual pinned interfaces were inspected locally, including their definitions
and relevant proof bodies:

| Dependency source | SHA-256 |
| --- | --- |
| FsFltz `Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| FsFltz `Geometry/CollarEvolution.lean` | `162ec4959c8d51f82c8bb6c59dff9074a84abf98dde4978d256d1851c1eaa361` |
| FsFltz `Geometry/CollarSmoothEvolution.lean` | `06b876a482369c6ad67119296417e69433650a24faae48b6d9d2d88ed4b74fd7` |
| Mathlib `Geometry/Manifold/IntegralCurve/UniformTime.lean` | `50b9021e83108d21b748395df9145ccf05b6eb3908d8cc6f40cbfb15b7d0b9f2` |

## Construction and mathematical meaning

1. **Inherited finite-interval existence is a proved input theorem.**
   `finiteIntervalExistence` chooses the compact proper sublevel
   `{y | P y ≤ P x + D}` before constructing any curve. A smooth cutoff with
   values in `[0,1]` preserves the scalar derivative bound. Its compact
   spacetime support satisfies the actual hypotheses of the pinned
   `CollarFlow.exists_global_solution`. The scalar displacement estimate then
   confines the constructed cutoff trajectory to the chosen sublevel for all
   times in `[0,1]`, where the cutoff is one. Thus its ODE becomes the original
   ODE, with full native derivatives even at the endpoints. There is no
   assumption of the desired flow and no circular confinement step.

2. **The new global field is auxiliary and constructed.**
   `extend_strip_field` uses normal separation of the closed spacetime strip
   from the complement of its given open smooth neighborhood. The smooth
   separator is one on the strip, with closed support inside that neighborhood.
   The inherited product-tangent-bundle cutoff bridge proves global section
   smoothness. Compact support is neither claimed nor needed at this step.
   `smooth_scalar_rate` uses the actual tangent map of `P`, so its scalar is
   exactly `dP(Z)`. `globally_bounded_extension` applies a smooth real bump to
   this rate, with inner and outer radii `D+1` and `D+2`. It remains one on the
   original strip, and outside the outer radius the new field vanishes. The
   resulting field agrees exactly with the input on `[0,1]` and has globally
   bounded scalar rate. No bound on the original off-interval field is assumed.

3. **All-real auxiliary trajectories are proved before smooth dependence.**
   For any initial time `s` and finite horizon `a`,
   `global_solution_of_scalar_bound` puts `b = |a|+1` and rescales time by
   `s-b+2*b*t`. The midpoint initial time is `1/2`; the rescaled field is
   `2*b` times the original field, with correspondingly rescaled scalar bound.
   The already proved finite-interval theorem therefore supplies each finite
   trajectory. The derivative calculation cancels the nonzero time scaling.
   The lifted field is literally the pinned native suspension `(1,Z)`, not a
   parameter-preserving lift with zero time component. Mathlib's
   `exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo` glues the finite
   suspended trajectories using native uniqueness. The suspended time
   coordinate is then proved equal to real time by uniqueness for derivative
   one. Projection gives actual global nonautonomous trajectories.

4. **Smooth diffeomorphisms are outputs.**
   `smoothEvolution_of_scalar_bound` chooses only those proved trajectories.
   The pinned `eq_of_hasMFDerivAt` proves their composition law and reverse-time
   inverses. The actual hypotheses of
   `CollarFlow.contMDiff_joint_of_hasMFDerivAt` are now available: a globally
   smooth real-time field, all-real trajectories, and their initial-value
   equation. Its joint smoothness conclusion includes initial time, final
   time, and initial point. Smoothness of both time slices and their reverse
   slices constructs native Mathlib `Diffeomorph` values. No smooth solution
   family or inverse is an input to this construction.

5. **Closed uniqueness handles both joins and both time directions.**
   `extend_closed_curve` pastes a candidate on `[a,b]` to the constructed
   auxiliary trajectories on either side. Values agree at the joins by the
   initial-value identity. The native within derivatives also agree there;
   `HasMFDerivWithinAt.union`, followed by the neighborhood criterion, proves
   the full derivative. The casts through the model tangent fiber in the
   final source merely express equality of the actual field values at equal
   base points. The proof does not replace the geometric derivative.
   `unique_closed` uses `a = min s t` and `b = max s t`, applies all-real
   uniqueness, and restricts back to the closed segment. It treats `s=t`
   separately by the initial-value identity, avoiding an invalid derivative
   uniqueness claim on a singleton.

6. **The final contract is inhabited without changing its meaning.**
   `evolution_of_scalar_bound` restricts the auxiliary evolution to the original
   closed strip and transfers its native ODE through exact field equality.
   The previously proved chart chain rule supplies the actual
   `M.chartTangentMap` equation under its chart-source premise. Smoothness uses
   the auxiliary all-real evolution as an extension, which is stronger than
   the required open-neighborhood extension. Its off-strip ODE is not asserted
   to be the original Moser ODE. Composition, inverse evolution and closed
   uniqueness are all supplied. `SmoothEvolution.isotopy` uses
   `u ↦ H.map 0 (u*t)`, with inverse `H.map (u*t) 0`; both families are jointly
   smooth, and their endpoints are identity and the requested map.

7. **Original geometry and quantifiers are retained.**
   `firstPathFlow` applies the accepted input package for the same arbitrary
   admissible `G`, positive `C`, and arbitrary compact exception `K`.
   `firstPathFlow_of_growth` uses the unchanged `GrowthAtInfinity` consumer and
   the same chosen witness throughout. Both transfer to the literal
   `FirstPath.X`, definitionally also `MoserRegularity.firstField`. The metric
   remains `P.compatible.g`, and the original metric dual/operator inverse
   norm is unchanged. The scalar continuation argument introduces no chart
   norm in its place. The proofs work on arbitrary native `SmoothManifold d`
   with its established Hausdorff and second-countable manifold structure;
   they are not restricted to affine space. No metric completeness, complete
   Liouville primitive, primitive-growth bound, or strengthened taming
   hypothesis is added. All-real completeness is proved for the auxiliary
   system, not silently asserted for a Liouville primitive.

## Consumers, documentation, and verification limits

`FirstPathFlowFinalChecks.native_ode` obtains the actual literal first-field
ODE from a constructed evolution, for every initial and terminal parameter,
including 0 and 1. `inverse_and_isotopy` obtains genuine reverse transport and
the time-one smooth isotopy. `growth_consumer` constructs the same-witness
literal-field `Evolution` from the original growth hypothesis. None takes an
evolution as an input. The chart equation and joint smoothness are fields of
that constructed `Evolution`, not independently assumed consumer premises.

`docs/first-path-flow-final.md` accurately describes the inspected proof chain,
its auxiliary-field distinction, its original inputs, and the remaining
comparison-theorem work. It explicitly supersedes the historical partial
status records without changing those inherited bytes.

This reviewer read source and actual dependency interfaces and wrote only
this report. No independent Lean build or transitive axiom audit was run by
the reviewer. The author reported successful checks of `FirstPathFlow` and
`FirstPathFlowFinalChecks` before the warning-only edit, with a final serial
build/type/axiom audit being prepared separately. Those reports are not
represented here as independently inspected final receipts. Source inspection
found no `sorry`, `admit`, custom `axiom`, or opaque proof declaration in the
reviewed construction modules. Final kernel acceptance and the restriction to
`propext`, `Classical.choice`, and `Quot.sound` must be established by the
separate exact-source build and transitive audit receipts. This source review
does not certify private delivery ancestry or any remote publication.
