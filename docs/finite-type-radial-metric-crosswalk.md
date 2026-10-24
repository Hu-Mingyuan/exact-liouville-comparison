# Cylindrical native derivative and metric crosswalk

Mission 0b5b2f0c-3dfa-4741-ac55-30976cabd107, revision 1. Baseline
f8b5b6bcb56a18c0094d15fed4619ff100327e30. This is the local calculation in
the proof of `cor:liouville`, manuscript lines 402–409, not the corollary.

`FiniteTypeRadialMetric.Target` quantifies arbitrary `d`, the unchanged
`LiouvilleDomain d`, its unchanged `Completion`, the original compatible
structure `A`, its `CylindricalStructure`, and any native smooth real function
`R`. Its only additional premise `EndRadius C R` is the literal equality
`R(C.endMap(y,t)) = exp(t)` when `2 ≤ exp(t)`. The conclusion is the primitive
identity on every ambient tangent vector and the exact squared g-dual norm at
every `t > log 2`. No radius existence, compactness, lower bound, or properness
is needed or asserted here. The parent owns those constructions and integration.

The manuscript coordinate is `r = exp(t)`. The cylindrical field equation in
`Statement.lean` is expressed using the native `mfderiv` of `endMap` and says
`J(v,s) = (contactJ(v) + s Reeb, -alpha(v))` after pushforward. The primitive
on pushed vectors is literally `exp(t) alpha(v)` by `Completion.end_primitive`.
Native differentiation of the end equality must be proved on an open
neighborhood; no derivative identity is an input. Ambient tangent surjectivity
must be proved from the pinned local diffeomorphism interface (which handles
dimension zero by the empty boundary). Thus testing on end vectors is justified.

`SmoothManifold.scalarDerivative R x v` is evaluation of the native `mfderiv`.
The prescribed `A.g` is a native smooth Riemannian metric and `A.metric_eq`
identifies it with the actual exterior derivative `d beta(v,Jw)`.
`A.MetricTangent x` equips the same tangent vector space with that metric norm;
`A.covector` transfers a native continuous linear functional without changing
its values, using finite dimension to prove continuity. `A.dualNorm` is the
operator norm of this functional for the g tangent norm. The chart norm is
not substituted. The proof must establish the required norm identity.

`Completion.ambient` is the unchanged `CompleteLiouvilleManifold`: positive
contraction `d beta(Z,v)=beta(v)` and an actual jointly smooth `Flow ℝ`
satisfying the chart ODE for every real time. Using its time derivative to
identify the pushed `∂t` with `Z` requires a native derivative bridge; none is
assumed. No Moser flow or comparison data occurs in the inputs.

The target is a specification, not a proof. Before substantive proof it must
compile and receive independent source-bound review. Delivery also requires
actual proofs, a consumer, full declaration inventory, managed receipts,
source/dependency hashes, allowed-only transitive axiom audit, and final review.
Existing semantic modules and upstream dependencies remain read-only.
