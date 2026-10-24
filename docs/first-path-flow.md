# First-path global evolution: bounded work

Mission f03338c3 retains construction and integration of the first-path Moser
flow, including uniqueness, smooth dependence, inverse evolution and isotopy.
The mission is open. The compiled `FirstPathFlowStatement` is an output contract,
not a proved existence theorem. `ODEContinuationStatement` isolates finite-interval
curve existence as a prerequisite, also not yet proved.

Inputs are exact private commit 639183b158c1d05af687823fd3bc6a57c10fa4af;
`verification/first-path-flow/base-source.json` records API comparisons with the
prepared source overlay. The authoritative manuscript, accepted FirstPath and
MoserRegularity modules, dependency pins and old project remain unchanged.
No final PDF or GitHub publication is part of this bounded mission.

See `verification/first-path-flow/crosswalk.md` for native definitions, actual
reuse candidates and the endpoint neighborhood bridge. Statements and proof
results must be kept distinct; no consumer of an assumed global flow is accepted
as a construction. The first-path regularity/scalar consumer and final evolution
assembly remain with this mission even when a generic prerequisite is delegated.

## Proved partial results

- `ODE.native_open_of_chart_family` and `native_open_of_interval_family` preserve
  the coefficient neighborhoods and construct their open native union.
- `ODE.chart_hasDerivWithinAt` gives the actual chart equation, including
  endpoint within derivatives, from the native nonautonomous equation.
- `FirstPathFlow.first_native_data` preserves any supplied growth witness and
  arbitrary compact exception. `first_growth_data` explicitly applies
  `MoserRegularity.first_growth_consumer` and `first_intervalSmooth` to the same G,
  obtaining native open smoothness and the proper scalar bound for literal X.
- `ODE.scalar_hasDerivWithinAt` proves the native scalar chain rule.
  `scalar_displacement` proves |P(γ(t))-P(γ(s))|≤D|t-s| on any convex interval
  inside [0,1]. `compact_sublevel` and `compact_confinement` give a compact set
  selected before any trial curve, valid in both directions.
- `FirstPathFlowChecks.exact_endpoints` exposes literal X at 0 and 1.

## Remaining owned gap

No `Evolution` has been constructed, and neither `Target`, `GrowthTarget` nor
`FiniteIntervalExistenceTarget` is proved. The proved confinement estimate is
conditional on an existing curve and is not represented as existence.
Child mission 0026c84b-1562-4164-9556-7e47f857440a owns only generic native
finite-interval existence. Parent mission f03338c3 retains all full-interval
flow integration, uniqueness, smooth dependence, evolution/inverse laws,
identity-start diffeomorphism isotopy, and source-bound repair/acceptance.
There is no correction or removal of the mission's required criteria.
