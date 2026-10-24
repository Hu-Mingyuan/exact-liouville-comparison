# Radial interpolation flow statement crosswalk

Mission 49efc076 revision 1, objective fd3670b6 revision 1. Source is the unchanged
`docs/reference/exact_liouville_comparison.tex`, Lemma `lem:bridge` and paths two/four.
The versioned roadmap c040da49e:docs/objective.md was read via the repository API.
The two new statement modules compile (managed source key
294beda7a483e42c6731cd284e23e60b35d8cb7eb6b80333ebc18388e41b05e6).
This is a statement gate, not a flow construction or mission acceptance.

| Source requirement | Literal Lean meaning |
| --- | --- |
| Arbitrary finite-dimensional smooth real manifold without boundary | Unchanged FsFltz `SmoothManifold d`, native Mathlib charts and `M.Tangent` |
| Symplectic reference beta, compatible J and explicit g | `RadialReference`, `CompatibleStructure`; g.inner is d beta(v,Jw); `MetricTangent`, `Dual`, `dualNorm`, `inverseNorm` retain g and its induced norms |
| Proper R >= 1 and compact-core exception | `P.smooth_R`, `proper_R`, `lower_R`, `radial_identity`, `radial_bound`, only outside R > rstar |
| Positive smooth coefficients, constant on core, rho+r rho'>0 | `RadialCoefficient P.rstar`, genuine `ContDiffOn` on Ici 1 and `derivWithin` at its endpoint |
| rho1 >= rho0 and r rho0 -> infinity | Explicit order on Ici 1 and `Tendsto ... atTop atTop` in `RadialInterpolationFlow.Target` |
| Smooth sigma, possibly degenerate d sigma | `M.IsSmoothForm sigma`, `RadialInterpolation.WeakDifferential`; no nondegeneracy of d sigma |
| mu_u=sigma+rho_u(R) beta | Existing `primitive` and `coefficient`; `primitive_parameter_derivative` proves the actual derivative delta(R) beta |
| i_X d mu=-dot mu | Target uses `RadialInterpolation.vector` literally; `vector_equation` and `vector_unique` give the intrinsic negative covector equation |
| All times, both directions and endpoints | `FirstPathFlow.Evolution` ranges over all pairs of `Parameter = Icc 0 1`, in initial/terminal order, every native point |
| Actual trajectories and uniqueness | `IsSolution` contains continuity and native `HasMFDerivWithinAt`; `solves` on Icc, `unique` on unordered closed intervals; `chart_solves` uses actual chart and tangent map |
| Smooth diffeomorphisms and joint smoothness | `map : Parameter -> Parameter -> M.SmoothEquiv M`; `extension` smooth on an open neighborhood of the closed double-time spacetime strip, not a uniform exterior strip |
| Evolution, inverse, isotopy | `initial`, `compose`, `inverse`, and `SmoothlyIsotopicToIdentity` with smooth inverse family are required output fields |

No complete Liouville structure is asserted for these primitives or auxiliary
fields. Accepted complete Liouville terminology elsewhere still requires an
all-real actual flow with positive contraction. Cartan exactness is excluded.
Equal coefficients, critical points and unrestricted upper coefficient growth
are not excluded by any new hypothesis.

## Separate analytic prerequisite

`ODE.TwoBarrierEvolutionTarget` has only native smoothness and scalar hypotheses,
not trajectories. R is smooth proper bounded below. Q is an actual jointly smooth
real function on real time times the manifold. Its sublevels uniformly bound R
for time in Icc 0 1. The partial derivative `deriv (fun u => Q u x) t` is the
ordinary real derivative. The total rate adds the actual `M.scalarDerivative`
in direction Z. Hypotheses are XR <= C0, partial_t Q >= 0, and
partial_t Q+XQ >= -C1, with nonnegative constants. These are exactly sufficient
for cutoff stability: partial_t Q+chi XQ is chi times the total rate plus
(1-chi) partial_t Q. Forward R and reverse Q are separate barriers; no absolute
common scalar derivative bound is assumed. Its conclusion is the same full
`Evolution`, including open joint smoothness and closed uniqueness.

Applicability obligations owned by the interpolation mission: construct the
open smooth extension of the literal field using `interpolation_intervalSmooth`
and `native_open_of_interval_family`; show Q(t,x)=Q_t(R(x)) is jointly smooth
(using smooth rho_i(R)); prove its partial derivative is delta(R)R >= 0;
use `interpolation_global` for global one-sided bounds; turn
`uniform_exhaustion` into its sublevel implication. Prove consumers using the
delivered small k and large A, plus zero sigma, unit coefficient and degenerate
cases. These obligations are not hidden in the final target.

## Reuse and evidence boundaries

Inspected Mathlib IntegralCurve/ExistUnique and UniformTime first: actual local
existence/uniqueness and assembly interfaces, not this two-barrier theorem.
FsFltz CollarSmoothEvolution requires constructed all-real solutions for its
joint smoothness theorem; its local smooth-solution theorem and compact-support
existence infrastructure can be reused with their hypotheses proved. Prior
cluster-skeleton reuse evidence is retained in the accepted crosswalk; its
specific complete cluster field is not an arbitrary nonautonomous flow theorem.
Existing `ODEContinuation` proves finite existence under absolute scalar control;
`ODEGlobalField` and `ODESmoothEvolution` also require that stronger control.
They cannot be applied to interpolation without a new proved bridge.

Local first-path source hashes match all 160 files in its final receipt; its
remote delivered head is c8df2c59abe2fd72b241c5b2bffddbe422e93693. This includes
regularity and interpolation inputs. Large A at 1c07d33b09b9b45fc99714173d09d50c32c9c52e
is on a separate branch and its three Lean modules are absent locally: explicit
integration and compatibility checks remain required before its consumers.
