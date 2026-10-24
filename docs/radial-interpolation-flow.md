# Radial interpolation flow: integration status

The full flow conclusion of manuscript Lemma `lem:bridge` remains open.
The compiled, independently reviewed target is
`RadialInterpolationFlow.Target`. This package proves its native analytic
applicability and coefficient specializations. It does not prove the general
two-barrier evolution theorem or Cartan exactness.

| Declaration | Proved content |
| --- | --- |
| `field_eq` | Literal equality with the accepted `RadialInterpolation.vector` |
| `barrier_smooth`, `barrier_time_derivative`, `barrier_time_nonneg` | Jointly smooth actual Q_u(R), its actual partial derivative delta(R)R, and nonnegativity |
| `barrier_sublevel` | Uniform reverse barrier sublevels bound proper R, with no upper-growth restriction |
| `of_twoBarrier` | Every hypothesis of the generic analytic target is discharged; explicitly conditional on that still-unproved target |
| `oneCoefficient`, `largeCoefficient`, `largeCoefficient_prime` | Actual unit and delivered A coefficients, including the ordinary/within derivative bridge at r=1 |
| `second_applicable`, `fourth_applicable` | Order, lower coefficient divergence, and weak taming for the literal k/A and 1/A cases |
| `second_rho`, `fourth_rho` | The manuscript's two affine coefficient formulas |
| `equal_evolution` | An actual full Evolution when the coefficients are equal; no divergence assumption needed in this special case |
| `critical_field_zero` | The vector vanishes at exterior critical points, including parameter endpoints |

The general adapter preserves arbitrary native manifolds, degenerate d sigma,
compact-core exceptions, endpoints, both directions, and unrestricted rho1.
`FirstPathFlow.Evolution` is reused without modification: actual native and
chart ODEs, closed uniqueness, open joint smooth extension, native smooth
diffeomorphisms, composition/inverse identities and smooth identity-start
isotopy are its output obligations. No Moser flow is an input to the main target.

## Exact inputs and reviewed statement gate

The private statement gate commit is
`70cb5f533db3755922378f2324a928398ac4b3a2`, based on first-path final commit
`c8df2c59abe2fd72b241c5b2bffddbe422e93693`.
Large A's fifteen delivery files are integrated additively from separate commit
`1c07d33b09b9b45fc99714173d09d50c32c9c52e`, preserving their exact bytes.
`verification/radial-interpolation-flow/inputs.json` records the retained source
hashes. Regularity 639183b and interpolation df00e843 are already included in
the first-path base; small k 4bb94fa4 is shared. The authoritative manuscript,
accepted geometry, earlier packages and aggregate import file remain unchanged.

The statement/crosswalk review is `statement-review.md` (artifact
ded5d271-0d3c-4e2c-8b99-1019849a0a6c); the bounded implementation review is
`input-proof-review.md`. Both distinguish specifications, conditional adapters,
special-case constructions, and the unproved general theorem.

## Owned remaining work

- Generic analytic construction: child mission
  `c88064ba-ac8f-4ffe-b3aa-85315df3b9bf`, assignment
  `33e55321-24f6-43f9-b5eb-4d5ed623cd68`, owns the unchanged
  `ODE.TwoBarrierEvolutionTarget` through full smooth Evolution, including
  forward R/reverse Q confinement, continuation and smooth-dependence bridges.
- This mission `49efc076-e2c9-4fa3-bcb9-a88475037526` retains integration,
  recovery on child failure/cancellation, unconditional flow consumers, final
  exact-source checks and independent flow proof review. Its obligation remains open.
- Root `040e593e-7a38-4959-9158-1caffe4e49fa` retains third path, Cartan
  exactness, comparison/corollaries and full acceptance.

This decomposition follows the actual interface gap: the inherited first-path
construction requires an absolute derivative bound for one scalar. Interpolation
supplies two different one-sided barriers. No mission criterion was removed or
weakened. The analytic child is distinct prerequisite work; integration stays here.

## Verification

Run `python3 scripts/verify-radial-interpolation-flow-inputs.py`. Under Horizon it
uses managed serial Lean checks and the existing pinned caches. It builds both
input branches, prints every new declaration type, audits transitive axioms,
checks the manuscript/dependency pins and preserved input hashes, and records
one exact source fingerprint. Only propext, Classical.choice and Quot.sound are
allowed. The conditional adapter's audit does not discharge its premise.

The manual CI workflow is supplied but remote CI execution is not claimed.
No GitHub upload, final PDF, complete Liouville claim or full-flow acceptance
is part of this input package.
