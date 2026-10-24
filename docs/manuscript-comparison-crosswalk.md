# Bounded application and manuscript assembly

Mission 7d0fe0b7-a970-4cef-ae30-6b624452f600 revision 1. Before proof, the
compilable FiniteTypeComparisonStatement and ManuscriptComparisonStatement
name the unchanged targets and specify the explicit native conclusion. A Prop
alias or conjunction is not a proof; actual theorem terms are still required.
Statement.lean, Geometry.lean, all imported semantic source and dependency pins
are preserved byte for byte. No definition correction is proposed.

| Source | Unchanged target and delivered/application term | Presentation and scope |
| --- | --- | --- |
| thm:main | MainTarget; MainComparison.mainTarget | Arbitrary dimension d, native smooth real manifold without boundary, exact beta and lambda, compatible J and explicit g, smooth proper R>=1, c>0, rstar>1, radial identities only where R>rstar. Weak taming is nonnegative, with separate nondegeneracy. Every admissible B on [1,infinity), positive C and compact exception. No completeness or primitive-growth input. |
| cor:liouville | FiniteTypeTarget; new finiteTypeTarget application | Actual FsFltz LiouvilleDomain and Completion; original CompatibleStructure A and CylindricalStructure. End coordinate t=log r. Eventual uniform estimate has existential B,C0,t0 with C0>0,t0>=0 and all y,t>=t0. Output compares T.primitive with C.ambient.primitive. No completeness assumption on T. |
| cor:stein | SteinTarget; SteinComparison.steinTarget | Input ProperComplexEmbedding on native real tangents: smooth proper embedding, injective differential, J square=-id and Cauchy–Riemann equation. Output SteinReference is constructed before T is quantified. It is not PackagedSteinTarget alone. beta=-(1/4)dR composed J, R=e+norm(i)^2 and g is exactly induced Euclidean metric. Growth lower endpoint is e; the delivered smooth extension and compact enlargement discharge the main input. No finite-type input. |
| cor:two | CommonReferenceTarget; CommonReferenceComparison.commonReferenceTarget | Independent B_i,C_i and compact exceptions. Delivered explicit consumer gives Phi=F1 composed F2 inverse and q=(h1-h2) composed F2 inverse. |
| Complete Liouville terminology | CompleteLiouvilleComparisonTarget; new specialization of mainTarget | Both specified primitives carry CompletePrimitive, with actual jointly smooth Flow real and coordinate ODE for every real t. Positive contraction d lambda(Z,v)=lambda(v). No new completeness hypothesis enters MainTarget. No completeness or Liouville-field conjugacy is deduced from an exact gauge. |

## Exact equality and growth bridge

FiniteTypeRadial.reference C A cyl is
(constructedRadius C A cyl).toReference. Radius.toReference sets exactStructure
literally to completionReference C and compatible literally to A, with c=1,
rstar=2 and R=FiniteTypeRadial.radius C. completionReference C uses exactly
C.ambient.primitive. Thus J, g.inner, g tangent norms, dualNorm and inverseNorm
are definitionally identical; the application will expose reflexive equality
lemmas and the weak-taming iff, not substitute a chart metric.

reference_growth C A cyl T takes exactly the existential end-growth premise of
FiniteTypeTarget. growth_witness chooses the complement of farEnd at
max t0 (log 2), proves compactness, and uses radius_end_eq. It retains the
original B and C0. Construction proves smoothness, properness, R>=1, R=exp t
for exp t>=2, R<=2 on the complement, beta=-dR composed J and dualNorm(dR)^2=R
when R>2. None of these is an additional application assumption.

The proof route is a direct application of MainComparison.mainTarget to this
reference and reference_growth; then assemble four actual proofs into the
unchanged ManuscriptTarget. CompleteLiouvilleComparisonTarget specializes the
same main theorem while retaining both prescribed CompletePrimitive parameters.
Native consumers must expose actual Diffeomorph F, jointly smooth H and inverse
family on [0,1], H0=id, H1=F, smooth h and literal primitive/exterior identities.

## Native definitions, reuse and presentation coverage

Mathlib was inspected first: native TangentSpace and mfderiv, Diffeomorph and
its inverse/composition, continuous alternating forms and Euclidean extDeriv,
ContMDiffOn, Bundle.ContMDiffRiemannianMetric, IsProperMap and interval integrals.
Pinned FsFltz Smooth.lean defines Form as native continuous alternating forms
on TangentSpace, exteriorDerivative by extDeriv transported through chart
maps, pullback by mfderiv, and SmoothEquiv as Diffeomorph. Existing project
bridges prove the required chain, exterior and isotopy laws for these actual
operations. No new geometric operations are introduced here.

Geometry.CompatibleStructure.metric_eq fixes g=d beta(.,J.). MetricTangent
installs this inner product on the same tangent space, covector retains the
same linear functional with g-dual norm, and inverseContraction is constructed
from nondegeneracy and finite dimension, using positive contraction. inverseNorm
is its operator norm g-dual to g, not the chart operator norm.

FsFltz Completion contains an actual CompleteLiouvilleManifold, a compact domain
with extension and boundary presentation, inclusion, complete-flow endMap,
end embedding/immersion, exact exp(t) alpha formula, covering and overlap.
CylindricalStructure expresses J(∂t)=Reeb and J(v)=contactJ(v)-alpha(v)∂t;
contactJ is independent of t. The reference J is chosen as in the manuscript;
existence of a compatible cylindrical J is not asserted by FiniteTypeTarget.

Mandatory cluster-skeleton inspection: read
/var/lib/archon-worker/imports/project-reference/archon_liouville/cluster-source-2c239b0/
Hu-Mingyuan-cluster-skeleton-2c239b0c03922a1549f18ee3a45a8e0ca25bb28c/
ClusterSkeleton/GeometryTarget.lean, LiouvilleData and its
 toCompleteLiouvilleManifold. These preserve the same field, primitive, complete
flow and positive sign. The cluster-specific carrier supplies no missing
comparison application; reuse the delivered general theorem and pinned native
interfaces instead. No infrastructure is required beyond equality/application
lemmas and conclusion unpacking.

Source-presentation boundary (not silently claimed as proved): the four formal
statements are on FsFltz SmoothManifold and the explicit Completion and
ProperComplexEmbedding presentations. This mission does not construct these
presentations from an independently defined intrinsic manifold-with-boundary
completion, nor a bridge from Mathlib complex-manifold holomorphic embeddings
to ProperComplexEmbedding. The latter records the native real Cauchy–Riemann
data needed for the argument, and the Stein reference is actually constructed
from it. General intrinsic presentation equivalence and cylindrical-J existence
are outside these unchanged targets. These are presentation coverage limits
for final exposition/acceptance, not additional inputs hidden in the proofs.
All four unchanged targets themselves must be proved; root retains any broader
source-presentation acceptance decision and final packaging.

## Exact source provenance

Main delivery: 55493c9ba47cc09071f6abf0b16b901a95f19b1f.
Stein/common-reference: 41e7528a6d0de96a657a7f570e0537bd5343a0fc, based on that
main delivery, with source-bound reviews and import manifest.
Finite-type reference/growth: ebedffcffe9b1098ee28359e5fd00adc9cd05ad8,
preserving reviewed implementation 9acd2ca5be07c490e1d9d48ac3e938390ac9a987 and
metric child 9716da2fdab7d268cfea6fbc3808a40cf3a47546. Producer obligation
7dadec84-89bb-40db-87dc-93a58b0c1992 is completed. Exact imports and preserved
review bindings are recorded under verification/manuscript-comparison.
