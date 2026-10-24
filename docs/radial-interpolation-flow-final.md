# Constructed radial interpolation flow

`RadialInterpolationFlow.radialInterpolationFlow` proves the unchanged reviewed
`RadialInterpolationFlow.Target`. It constructs the full native smooth Moser
evolution of the literal accepted `RadialInterpolation.vector` for every pair of
parameters in `[0,1]`, on every accepted native radial manifold. There is no
remaining flow, continuation, growth, or completeness premise.

This delivery supersedes the open-flow status in the historical input report
`docs/radial-interpolation-flow.md` and its receipts. Those audited files are
preserved byte for byte. The original statement and independently reviewed
definition crosswalk in `verification/radial-interpolation-flow/` are unchanged.
No mission correction or acceptance criterion was removed.

## Proof and definition crosswalk

The accepted reference `RadialReference` retains its explicit compatible metric
g, the actual differential of beta, its almost complex structure, proper R >= 1,
and the compact-core exception. The accepted metric tangent, dual and operator
norms are unchanged. `RadialCoefficient` retains positivity, smoothness on
`Ici 1`, constancy on the core and positivity of rho + r rho'. The theorem adds
exactly coefficient order and divergence of r rho0, and permits degenerate
d sigma. It makes no restriction on upper-coefficient growth.

| Proved declaration or module | Mathematical role |
| --- | --- |
| `field_eq` | Literal equality of the regularity field and accepted inverse-contraction vector; its sign and actual Moser equation remain those of `RadialInterpolation.vector_equation`. |
| `of_twoBarrier` | Discharges the generic theorem's native open bundle smoothness, proper scalar, moving barrier and one-sided rate hypotheses. Its former premise is now supplied by a proof. |
| `barrier_smooth`, `barrier_time_derivative`, `barrier_time_nonneg` | The actual Q(t,x)=R(x)rho_t(R(x)) is jointly smooth, with partial derivative delta(R)R >= 0. |
| `barrier_sublevel` | Uniform Q sublevels bound R, using only lower-coefficient divergence and order. |
| `ODETwoBarrierConfinement` | Proves native chain rules, forward R and reverse Q displacement estimates and compact confinement from initial data. |
| `ODETwoBarrierExistence` | Constructs compactly supported auxiliary solutions, proves confinement, then proves that the cutoff is one along the whole closed-interval trajectory. |
| `ODETwoBarrierLocalization`, `LocalizationPatch`, `SmoothAssembly`, `Smooth` | Prove native closed uniqueness and chart bridges; localize around finite trajectories; assemble joint smooth dependence and actual diffeomorphism evolution. |
| `ODE.twoBarrierEvolution` | Constructs the entire unchanged generic `Evolution` from those proved finite trajectories. |
| `radialInterpolationFlow`, `evolution` | Prove the reviewed radial target and select its constructed evolution. |

Forward trajectories obey R(gamma(t)) <= R(x)+C0(t-s). Reverse trajectories
obey Q(t,gamma(t)) <= Q(s,x)+C1(s-t). These different bounds yield one compact
R sublevel for each initial datum. Multiplication of the field by a cutoff in
[0,1] preserves both bounds: the reverse rate is the cutoff times the original
total rate plus (1-cutoff) times the nonnegative partial time rate. No common
absolute scalar derivative estimate is asserted or used.

`Evolution.map` is a native smooth diffeomorphism for all source and target
parameters. Its real double-time extension is jointly smooth on an open
neighborhood containing the entire closed square times M; no uniform exterior
time margin is required. `solves` supplies continuity and the actual native
within derivative at both endpoints. The construction first obtains full native
derivatives there. `chart_solves`, `unique`, `initial`, `compose`, `inverse` and
`isotopy` supply the actual chart equation, uniqueness on unordered closed
intervals, identity/evolution/inverse laws and an identity-start isotopy with
jointly smooth forward and inverse families. None of these is an input field.

## Unconditional consumers

`RadialInterpolationFlowChecks` imports the proof, not merely its target.

| Theorem | Result |
| --- | --- |
| `native_ode` | Literal-vector trajectories through every initial time and point, on all of the closed interval. |
| `sigma_zero` | Full evolution for the degenerate differential d sigma=0. |
| `unit_start` | Full evolution for rho0=1 and arbitrary ordered rho1. |
| `second_path` | Full evolution for the delivered literal k and A and weakly taming exact-symplectic primitive. |
| `fourth_path` | Full evolution from beta to A beta; its inverse endpoint is the fourth manuscript arrow. |
| `equal_identity` | Actual identity evolution for equal coefficients, even without lower-coefficient divergence. |
| `critical_fixed` | The general constructed evolution fixes all exterior critical points covered by the accepted radial identity. |
| `endpoint_inverse_isotopy` | Actual inverse endpoint diffeomorphisms and identity-start smooth isotopy. |

`second_applicable`, `fourth_applicable`, `second_rho` and `fourth_rho` retain
the previously proved k/A and 1/A hypotheses and literal coefficient formulas.
No radial critical-point identity is imposed on the compact core.

## Exact-source integration and verification

The private input base is `a5bccccea792f4e81f1f2c917d02f1c542a06f21`.
The generic child delivery is `7afe8014aae719630d0969d0bcfc28f29e9ab3b7`,
mission `c88064ba-ac8f-4ffe-b3aa-85315df3b9bf`. Its exact source and independent
component reviews are integrated additively. Shared source hashes agree.
The first-path, interpolation, regularity, small k, large A, manuscript and
upstream dependency bytes remain unchanged. The unrelated aggregate import
is unchanged; consumers import the dedicated module directly.

Run `python3 scripts/verify-radial-interpolation-flow-final.py`. Under Horizon,
all Lean checks run serially through `horizon-lean-check` using managed caches.
The script checks preserved input hashes and dependency pins, builds the final
consumers, prints the complete explicit declaration/type inventory and actual
contract structures, and audits every listed declaration transitively. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. It records exact
source hashes and requires one verified source fingerprint across the checks.
The independent final source review and machine receipt live in
`verification/radial-interpolation-flow-final/`. The manual CI recipe is
provided; remote CI execution is not claimed.

This bounded mission delivers the flow part of `lem:bridge` and its path-two
and path-four consumers. Root mission `040e593e-7a38-4959-9158-1caffe4e49fa`
retains third path, Cartan exactness, comparison/corollaries and overall
acceptance. Finite-interval Moser evolution is not called a complete Liouville
flow. No authoritative manuscript edits, GitHub upload or final PDFs are made.
