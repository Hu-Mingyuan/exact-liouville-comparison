# Constructed first-path global smooth evolution

`ExactLiouvilleComparison.FirstPathFlow.firstPathFlow` proves the unchanged
`FirstPathFlow.Target`. `firstPathFlow_of_growth` proves `GrowthTarget`, and
`evolution` chooses the actual constructed result. This completes the bounded
first-path ODE construction; it does not prove Cartan exactness, the remaining
paths, the comparison theorem or any final corollary. Mission acceptance by the
integration maintainer remains distinct from the source delivery.

The earlier `docs/first-path-flow.md` and its verification package are historical
partial-delivery records, retained byte for byte. Their open existence gaps are
closed by the proofs described here. No statement, manuscript, dependency,
FirstPath or MoserRegularity input is changed.

## Input and output

Inputs remain an arbitrary native `SmoothManifold d`, the accepted radial
reference `P`, weakly taming exact symplectic form `T`, and arbitrary admissible
`G : AdmissibleGrowth 1`, with the original positive constant and arbitrary
compact exception in the inverse-norm bound. The reference metric is
`P.compatible.g`; the original dual/operator norms are unchanged. The growth
consumer starts from the original `GrowthAtInfinity` and uses its same witness
through smoothness, exhaustion, and the literal `FirstPath.X`. Neither metric
completeness nor a complete Liouville hypothesis is present.

For every initial and terminal parameter in [0,1] and every point, the constructed
`Evolution` contains a native smooth diffeomorphism and its actual trajectory,
closed-interval native ODE, native-chart ODE, uniqueness on the unordered closed
interval, joint smooth extension around both endpoint parameters, evolution and
inverse identities, and identity-start smooth diffeomorphism isotopy. The
smooth inverse family is part of the accepted isotopy definition.

## Proof chain

1. `FirstPathFlow.first_native_data` and `first_growth_data` use the delivered
   `MoserRegularity.first_intervalSmooth` and `first_growth_consumer`. The
   `ODE.native_open_of_interval_family` bridge retains the open chart coefficient
   neighborhoods and takes their native open union. A `NativeJoint` hypothesis
   alone is not used as an open-neighborhood theorem. The actual exhaustion is
   `log (S (R x))`, smooth, proper, bounded below, with a uniform scalar derivative
   bound on the full closed strip.
2. `ODE.finiteIntervalExistence`, delivered by child mission 0026c84b, chooses a
   compact proper sublevel before the curve. A bounded compact spacetime cutoff
   permits the pinned constructed compact-support solution theorem. The proved
   scalar displacement bound confines that curve to the sublevel, where the
   cutoff is one. It therefore solves the original field on [0,1], with full
   native derivatives even at the endpoints.
3. `ODE.extend_strip_field` constructs a smooth global extension using normal
   separation and a smooth cutoff whose closed support lies in the original
   open neighborhood. `globally_bounded_extension` then multiplies by a scalar
   bump of the smooth actual derivative of the exhaustion. Its radii are D+1
   and D+2, so it is one on the whole original strip and globally bounds the
   auxiliary scalar derivative by D+2. There is no claim that the original
   Moser field is controlled for all real times.
4. `ODE.global_solution_of_scalar_bound` rescales the proved finite-interval
   theorem to every finite horizon. Actual native time suspension and Mathlib's
   finite-to-global integral-curve theorem assemble all-real auxiliary curves.
   The time coordinate is proved to be the real parameter by uniqueness.
5. `ODE.smoothEvolution_of_scalar_bound` chooses those constructed curves.
   Native uniqueness proves composition and inverse identities. The pinned
   `CollarFlow.contMDiff_joint_of_hasMFDerivAt` theorem now applies to proved
   all-real solutions and gives smooth dependence on both times and the point.
   This constructs native `SmoothEquiv` values, not merely bijections.
6. `ODE.SmoothEvolution.extend_closed_curve` pastes any closed-interval solution
   to auxiliary trajectories on both sides. Matching within derivatives and
   their unions prove the full ODE at the two joins. All-real uniqueness then
   proves `unique_closed`, in either time direction. The equal-time case is
   immediate. `SmoothEvolution.isotopy` gives the identity-start family and
   proves both it and its inverse smoothly depend on parameter and point.
7. `FirstPathFlow.evolution_of_scalar_bound` restricts the constructed auxiliary
   evolution to [0,1]. Exact field agreement gives the original native ODE;
   `ODE.chart_hasDerivWithinAt` gives the actual chart equation. The two final
   first-path theorems apply the original native inputs to this construction.

The reuse search was performed in order: pinned Mathlib, pinned FsFltz, then the
previous cluster-skeleton source. Exact signatures and the original search are
recorded in `verification/first-path-flow/crosswalk.md`; the final bridge
crosswalk is in `verification/first-path-flow-final/crosswalk.md`. New modules
address the verified gaps between those signatures. No criterion was removed
or weakened. The finite-interval prerequisite was a distinct child outcome;
this mission retains integration and source-bound repairs.

## Reproduction and evidence

Run `python3 scripts/verify-first-path-flow-final.py`. In the managed Horizon
workspace it uses `horizon-lean-check`; outside that environment it uses the
pinned Lake toolchain. It verifies retained input hashes, builds the final
consumer module, prints fully qualified types, audits transitive axioms, and
records exact source hashes. Its managed checks must share one verified source
fingerprint. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The statement was compiled and independently reviewed before substantive proof
work; see the unchanged `verification/first-path-flow/statement-review.md`.
The final source-bound independent proof assessment is
`verification/first-path-flow-final/proof-review.md`. This proof package extends
private commit `3be213d6b2061ce31d0f52638cb68fe87c478d0b`, itself an exact
extension of `1ec91645f801288f06b158a050c098f5511b9071` and the required regularity
base `639183b158c1d05af687823fd3bc6a57c10fa4af`. Publication and verification are
bound by a separate delivery artifact. No final PDF or GitHub upload is made.
