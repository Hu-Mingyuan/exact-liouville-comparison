# Final construction crosswalk

The unchanged `FirstPathFlowStatement.lean` was compiled and independently
reviewed before proof work (SHA-256
`2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217`).
Its `Target` and `GrowthTarget` are now the types of actual proved theorems.
The earlier statement crosswalk and its review remain authoritative for the
source assumptions and literal first path; this document records construction.

| Required outcome | Actual declaration / bridge |
| --- | --- |
| Literal `FirstPath.X`, arbitrary admissible B and compact exception | `FirstPathFlow.firstPathFlow`, `evolution`; unchanged `first_native_data` |
| Original GrowthAtInfinity input, same G | `FirstPathFlow.firstPathFlow_of_growth`; unchanged `first_growth_data`, using `MoserRegularity.first_growth_consumer` and `first_intervalSmooth` |
| Open native endpoint regularity | `ODE.native_open_of_interval_family`, `native_open_of_chart_family` retain chart neighborhoods; `ODE.extend_strip_field` extends their actual native union |
| Actual smooth scalar rate | `ODE.smooth_scalar_rate` uses native tangent map of the smooth exhaustion |
| Controlled all-real auxiliary field, exact strip agreement | `ODE.globally_bounded_extension`; the smooth scalar-rate bump is one throughout [0,1] |
| Every initial point/time, both directions and endpoints | Proved `ODE.finiteIntervalExistence`, then `global_solution_of_scalar_bound` and restriction in `FirstPathFlow.evolution_of_scalar_bound` |
| Native ODE | `Evolution.solves` constructed from `SmoothEvolution.solves`; final `FirstPathFlowFinalChecks.native_ode` exposes literal X for every closed parameter |
| Actual native-chart ODE | `ODE.chart_hasDerivWithinAt`, applied to every chart whose source contains the trajectory point |
| Closed-interval uniqueness | `ODE.SmoothEvolution.extend_closed_curve` and `unique_closed` paste on both sides and prove endpoint derivatives by union |
| Joint smooth dependence including endpoint neighborhoods | `ODE.smoothEvolution_of_scalar_bound` applies proved pinned smooth dependence to constructed all-real curves; `Evolution.smooth` takes U = univ for the auxiliary extension |
| Diffeomorphisms, inverse evolution, composition | `ODE.SmoothEvolution` is constructed with actual `M.SmoothEquiv M`; inverse and composition follow from native ODE uniqueness |
| Identity-start isotopy, smooth inverse family | `ODE.SmoothEvolution.isotopy`; restricted `Evolution.isotopy`; `FirstPathFlowFinalChecks.inverse_and_isotopy` |

All declaration names above are under `ExactLiouvilleComparison`, except the
pinned names below. Full inferred types, source paths and transitive axiom
reports are emitted by the reproducible verification script. The actual `g`,
dual norm and inverse operator norm occur in the unchanged accepted radial,
compatible metric and weak taming definitions, reviewed earlier. No ODE output
is an input to `firstPathFlow` or `firstPathFlow_of_growth`.

## Actual pinned reuse

The original ordered reuse search is retained in
`verification/first-path-flow/crosswalk.md`: pinned Mathlib, pinned FsFltz,
then the previous cluster-skeleton. New construction addresses the exact gaps
between strip-local smoothness/proper control and the global interfaces.

- Mathlib smooth partitions of unity and bump functions construct cutoffs;
  `normal_exists_closure_subset` supplies an intermediate open set. No globally
  uniform neighborhood beyond the closed parameter strip is assumed.
- Child `ODEContinuation` proves finite existence using pinned
  `FsFltz.Geometry.CollarFlow.exists_global_solution` only after constructing
  a globally smooth field with compact spacetime support. Compact confinement
  proves that its solution is a solution of the original field on [0,1].
- Pinned `FsFltz.Geometry.CollarFlow.contMDiff_timeSuspension` constructs the
  smooth autonomous time suspension. Mathlib's
  `exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo` assembles all-real
  curves from proved finite solutions. A scalar uniqueness proof identifies
  the suspended time coordinate; the spatial projection satisfies the native
  nonautonomous ODE.
- Pinned `FsFltz.Geometry.CollarFlow.eq_of_hasMFDerivAt` proves uniqueness of
  all-real native solutions. Its globally smooth field hypothesis is proved
  by the cutoff construction, and its curves are supplied by the preceding
  existence proof.
- Pinned `FsFltz.Geometry.CollarFlow.contMDiff_joint_of_hasMFDerivAt` requires
  all-real solutions through every initial time/point. Those hypotheses are
  constructed by `global_solution_of_scalar_bound`, not added to the final
  first-path theorem.
- Mathlib `HasMFDerivWithinAt.union` and `HasMFDerivWithinAt.hasMFDerivAt`
  establish the two endpoint joins in closed-interval uniqueness.

No complete Liouville terminology or hypothesis is introduced for the auxiliary
ODE. The accepted complete Liouville definition elsewhere retains an actual
all-real flow and positive contraction convention. No geometric norm is
replaced by the model norm used internally for native chart/ODE machinery.

The finite-existence child has delivered exact commit
`3be213d6b2061ce31d0f52638cb68fe87c478d0b`, binding
`acc2ddbd-0520-41a0-a1e8-50efcfd6d4f3`. Its independent review and original
source package are retained. The present mission owns integration and repairs;
the root owns the remaining paths, exactness, comparison, and final acceptance.
