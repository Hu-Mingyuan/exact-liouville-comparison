# Independent statement and definition review

Reviewer: delegated statement reviewer, independent of implementation; 2026-10-23.
Scope: manuscript `lem:bridge`, the radial interpolation flow target, the separate
two-barrier analytic target, and the submitted definition crosswalk. No proof
implementation or concurrent Lean build was performed during this review.

**Verdict: pass the statement gate.** The two targets faithfully specify the
intended finite-interval existence problem and an applicable analytic prerequisite.
I found no circular existence input, omitted endpoint, sign reversal, hidden
strict taming assumption, upper-growth restriction, or extra metric completeness
assumption. This verdict authorizes substantive proof work; it does not establish
either target, or accept the manuscript theorem as proved.

## Exact reviewed artifacts

SHA-256 values read from the local files:

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/RadialInterpolationFlowStatement.lean` | `a9e8a8f144f240846f4b3e85ab26f78877aa063a2fbf2a478b78bf4c90c7d123` |
| `ExactLiouvilleComparison/ODETwoBarrierStatement.lean` | `81b206239999b41a479672cc5a73673115a5c09f3393d0438674bf2df794eb17` |
| `verification/radial-interpolation-flow/crosswalk.md` | `54ed4154d99265fbbbb29d6e63c2506fee66f59c7a1cca58d7f574068c87b732` |
| `ExactLiouvilleComparison/FirstPathFlowStatement.lean` | `2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |

I read `AGENTS.md`, `docs/objective.md`, the unchanged manuscript lemma and its
proof, the new modules and crosswalk, the imported definitions and producers
listed below. `statement-build.log` records a successful final managed build of
`ExactLiouvilleComparison.ODETwoBarrierStatement`, including both new modules,
`snapshot_verified: true`, source key
`294beda7a483e42c6731cd284e23e60b35d8cb7eb6b80333ebc18388e41b05e6`, Lean 4.34.1.
The initial out-of-date cache check in that log was followed by successful rebuild.
This is compilation evidence supplied by the build owner, not an independent rerun.
The manifest pins FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Definitions checked literally

* Pinned FsFltz `Smooth.lean` defines `SmoothManifold` using finite-dimensional
  native Mathlib charts, Hausdorff and second-countable topology, and the
  boundaryless model. `Tangent` is `TangentSpace`; forms are continuous
  alternating multilinear maps on those fibers. `exteriorDerivative` uses
  Mathlib `extDeriv` of actual chart coefficients transported by actual
  differentials. `scalarDerivative` is native `mfderiv` applied to a tangent
  vector; `SmoothEquiv` is Mathlib `Diffeomorph` at smoothness order infinity.
* `CompatibleStructure.g` is a native smooth Riemannian metric with
  `g.inner x v w = d beta(v,Jw)`. `MetricTangent` installs this metric's norm on
  the native tangent vector space. `Dual`, `covector`, and `inverseNorm` use the
  resulting dual/operator norms; `covector_apply` identifies the underlying
  covector. Inverse contraction is constructed by finite-dimensional
  nondegeneracy, not supplied as arbitrary inverse operations or an existence
  field. This interpolation target needs no additional inverse-form growth bound.
* `RadialReference` preserves proper `R >= 1`, positive `c`, `rstar > 1`, and
  the radial identity and dual-norm inequality only on `rstar < R`. Compactness
  of the core follows from properness and the lower bound. No completeness of
  the Riemannian metric is required.
* `RadialCoefficient` is positive and smooth on `Ici 1`, constant on the whole
  closed core interval, with positive `rho + r * derivWithin rho (Ici 1) r`.
  `smooth_comp` and `scalarDerivative_comp` already handle `R = 1` correctly.
  Coefficient interpolation includes both endpoints. No bound above on `rho1`
  appears, and equal coefficients are permitted.
* `WeakDifferential` is exactly `d sigma(v,Jv) >= 0` for all points and vectors.
  It does not require nondegeneracy. `exactStructure` proves the interpolated
  differential symplectic from these inputs. `vector` is the actual inverse
  contraction of `-delta(R) beta`; `vector_equation`, `vector_unique`, and
  `primitive_parameter_derivative` tie it to the manuscript's Moser equation.
  Symplecticity is therefore an existing proved producer, although the new
  flow target does not redundantly restate it as a conjunct.
* Pinned `Family.lean` defines `Parameter` and `parameterInterval` literally as
  `Icc 0 1`. `Evolution.map` quantifies every pair of initial and terminal
  parameters and every native point. Its `solves` field uses native
  `HasMFDerivWithinAt` with velocity map `v ↦ v • Z`, including endpoints;
  `chart_solves` uses the actual chart differential. `unique` works on `uIcc`
  and includes explicit continuity. The singleton interval causes no false
  uniqueness assertion: its endpoint conclusion is the initial identity.
* `Evolution` also requires actual smooth diffeomorphisms, composition,
  inverse, and smooth isotopy (including the inverse family). Its joint
  extension is smooth on an open neighborhood of the entire closed double-time
  strip; it does not demand one uniform exterior time strip at spatial infinity.
  These are output obligations, not assumed flows. `Target` and
  `TwoBarrierEvolutionTarget` are definitions of propositions, not their proofs.
* No auxiliary primitive is called a complete Liouville manifold here. The
  imported complete interface retains the positive contraction convention and
  actual `Flow R` for every real time, as verified in pinned `Liouville.lean`.

## Analytic target and applicability

The generic target's upper bound `ZR <= C0` controls proper `R` in forward time.
The lower bound `partial_t Q + ZQ >= -C1` bounds `Q` above in reverse time.
Uniform control of `R` by `Q` sublevels then confines each reverse trajectory
to a compact `R` sublevel. The lower bound on `R` makes these sublevels compact
from `IsProperMap R`. No absolute derivative estimate follows or is needed.
Joint smoothness of `Q` makes both displayed derivative terms genuine ordinary
derivatives. The additional `partial_t Q >= 0` is applicable to the manuscript
barrier and gives the stated stability under spatial cutoffs `0 <= chi <= 1`:
the new rate is `chi * (partial_t Q + ZQ) + (1-chi) * partial_t Q`.

The following applicability proofs are supported by the delivered inputs and
do not require extra assumptions:

1. `interpolation_intervalSmooth` constructs an extension from the actual
   affine form equation using `intervalSmooth_of_equation`, whose extension is
   the pointwise inverse solution. `native_open_of_interval_family` produces
   the required open native bundle-smooth field and exact agreement on the
   closed interval. Its smoothness neighborhoods are retained, not assumed.
2. Set `Q(t,x) = RadialInterpolation.Q q0 q1 t (P.R x)`. Its global joint
   smoothness follows by sums and products from `P.smooth_R`, the two existing
   `smooth_comp` theorems, and the time projection. No extension of arbitrary
   coefficient values below radius 1 is needed.
3. `Q_parameter_derivative` gives the actual time derivative
   `delta(R) * R`, nonnegative by coefficient order and `R >= 1`.
   `Q_scalarDerivative` and `barrierRate_eq` identify the spatial and total
   derivatives. `interpolation_global` supplies both global constants, with
   the compact core handled by actual compactness and smoothness.
4. `uniform_exhaustion` gives the sublevel implication. Use its threshold for
   **`L + 1`**, not merely `L`: if `Q <= L` and `R >= T`, the resulting
   `L+1 <= Q` is contradictory, so `R < T`. This is a small strictness bridge
   to prove in Lean, not a missing coercivity hypothesis.

## Remaining proof and acceptance obligations

The generic two-barrier existence theorem is still substantive work: construct
trajectories, prove finite-endpoint continuation in both directions, establish
closed-interval uniqueness, then construct the full open smooth evolution and
its diffeomorphism/isotopy fields. Reading Mathlib
`IntegralCurve/ExistUnique.lean` confirms actual local existence and uniqueness
interfaces. FsFltz `CollarSmoothEvolution.contMDiff_joint_of_hasMFDerivAt`
requires an already constructed all-real family and globally smooth field; it
cannot be applied directly to these open-neighborhood inputs. Localize or
construct the necessary cutoff/global bridges with proofs. The present scalar
hypotheses do not by themselves constitute those Lean proofs.

An explicit Lean consumer should discharge the applicability steps above and
transport the constructed evolution back to the literal interpolation field.
The small-coefficient/large-coefficient consumers and equal-coefficient, unit,
zero-sigma and degenerate-differential checks remain required. Large-coefficient
integration remains separate as acknowledged by the submitted crosswalk.
Final exact-source build, independent proof review and transitive axiom audit
are still required. This review neither audits all imported proof axioms nor
certifies any final theorem or publication artifact.
