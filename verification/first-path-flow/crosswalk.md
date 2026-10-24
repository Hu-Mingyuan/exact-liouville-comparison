# First-path ODE statement crosswalk

Mission f03338c3 revision 1; statement gate only, not flow acceptance.
The source input is private commit 639183b158c1d05af687823fd3bc6a57c10fa4af,
verified publication b8fbd479-3b1f-4a75-8b4e-3706a3d1b275 and binding
3f1b1913-086a-4079-8ca0-97d1c3d7e069. `base-source.json` compares 108 existing
source/verification files directly with that exact commit through the authenticated
repository-file API. All match. The extra local regularity plan is not part of the
input. The sandbox Git HEAD is an old skeleton; direct clone lacks Forge credentials.
Development therefore uses the verified exact source overlay, with private delivery
to be based explicitly on 639183b, never on the skeleton Git HEAD.
The versioned roadmap c040da49:docs/objective.md was read from repository e579622a.
The manuscript remains unchanged (SHA256 in docs/sources.json).

## Definitions and quantifiers

`FirstPathFlow.IsSolution` is the actual native `HasMFDerivWithinAt` equation
for a time-dependent tangent section, with explicit continuity on the parameter
set. Its linear derivative maps r to r times Z_t(gamma(t)). It is the
nonautonomous analogue of Mathlib `IsMIntegralCurveOn`, not a symbolic operation.
For the full interval it includes t=0 and t=1. Uniqueness uses `uIcc s t`,
so applies in either direction and also when s=t.

`Evolution Z` is output data: actual native smooth diffeomorphisms `map s t`,
one open jointly smooth extension in initial time, terminal time and point,
identity at equal times, native ODE, the actual derivative of every chart,
uniqueness, composition, inverse evolution and the accepted
`SmoothlyIsotopicToIdentity` conclusion for every identity-start slice.
No uniform off-interval strip is required. No constructor of this structure is
yet proved; a Target proposition is not mission acceptance.

`Target` quantifies over every accepted radial reference P, every admissible
G (hence arbitrary admissible B), exact symplectic T with nonstrict weak taming,
positive C and arbitrary compact K with the original inverse-norm bound outside K.
The field is `MoserRegularity.firstField`, definitionally
`FirstPath.X P G T hw x t.val t.property.1`. Its contraction sign is
+i_X(omega+t eta)=-k beta. `GrowthTarget` exposes this field literally and starts
with unchanged `GrowthAtInfinity`. The explicit reference metric is
P.compatible.g = d beta(.,J.); `inverseNorm` is the inverse positive
contraction operator norm from that metric dual to that metric tangent fiber.
No chart norm replaces these norms. No primitive growth, metric completeness,
complete-Liouville assumption, or global flow is added. This is a bounded
exact-symplectic Moser evolution, not a complete Liouville structure.

## Reuse investigation, in required order

1. Pinned Mathlib `Analysis/ODE/ExistUnique.lean` gives Picard–Lindelof local
existence and ODE uniqueness. `Geometry/Manifold/IntegralCurve/Basic.lean` gives
the actual native within derivative equation; `ExistUnique.lean` provides local
manifold curves and uniqueness. These do not directly construct the required
nonautonomous full-interval evolution with open endpoint regularity.
2. Pinned FsFltz `Family.lean` defines `IsSmoothIntervalVectorFieldFamily` as
one real extension with `SmoothNearInterval` open smooth coefficient neighborhoods
in every chart. `FamilyLiouvilleNeighborhood.contMDiffAt_familySection_of_chart`
converts an individual chart coefficient germ to the native tangent section.
The required bridge must retain the open neighborhoods and glue their inverse
images to get a native open neighborhood; pointwise `NativeJoint` is insufficient.
`ProperExhaustionCompleteFlow.exists_integralCurveOn_of_proper_exhaustion` and
`exists_completeFlow_of_proper_exhaustion` prove autonomous continuation.
`CollarSmoothEvolution.contMDiff_joint_of_hasMFDerivAt` proves smooth dependence
for all-real solutions of a globally smooth nonautonomous field; its hypotheses
cannot simply be asserted for the first path. `FamilyLiouvilleLocalFlow` supplies
compact cutoffs on genuine native neighborhoods, but its parameter-preserving
field has zero time component and is not the nonautonomous time suspension.
3. Previous cluster-skeleton at exact 2c239b0 was located via its recorded local
archive and inspected read-only: `GeometryTarget.lean`, `NativeCompleteFlow.lean`
and `verification/NativeCompleteFlowInterface.md`. The latter constructs genuine
autonomous all-real curves by supremum-of-lifetimes, uniform local lifetime on a
compact confinement set, and uniqueness-based splicing. It then invokes the same
FsFltz joint smoothness theorem. Its hypotheses are specialized to the cluster
field and its confinement theorem; no theorem directly accepts this first-path
nonautonomous field. The proof pattern can be generalized, but its complete flow
cannot be assumed. The old project is unchanged.

## Planned proof bridges and ownership

This mission owns the native open-neighborhood conversion from
`first_intervalSmooth`, the consumer of `first_growth_consumer`, and all first-path
integration. A reusable continuation prerequisite must construct finite-interval
solutions and smooth dependence from a native open time-space neighborhood plus
proper scalar bounds on [0,1]. Compact cutoffs and time suspension are available
proof ingredients; an unproved continuation package must never become a hypothesis
of the first-path theorem. No change to required outcomes or assumptions is proposed.
