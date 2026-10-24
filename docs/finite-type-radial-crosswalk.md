# Finite-type radial reference: statement crosswalk

Mission 9329795b-7d27-46a3-adb3-79b3711aaf56 revision 1. Versioned roadmap
86760810-08b9-4687-a4a9-37f6a45e361c revision 1 is
f8b5b6bcb56a18c0094d15fed4619ff100327e30:docs/sdu-continuation.md.
Source: unchanged manuscript cor:liouville, lines 375–408.
The new FiniteTypeRadialStatement module specifies bounded obligations only;
it does not prove them or the corollary.

## Exact inputs and outputs

ConstructionTarget takes exactly arbitrary d, LiouvilleDomain D, Completion C,
CompatibleStructure (completionReference C) A, and CylindricalStructure C A.
No radius, properness, compactness bridge, norm identity, MainTarget or Moser
flow is an input. Radius is OUTPUT data on the original C.ambient.manifold.
It supplies native smooth proper R≥1, equality R=exp(t) for exp(t)≥2,
bound R≤2 off the strict end t>log(2), compactness of that complement, and
the two literal exterior identities β=−dR∘J and dualNorm_A(dR)^2=R.
These fields are construction obligations, never assumptions offered as proof
of ConstructionTarget. RadialReference will be built with exactStructure
definitionally completionReference C, compatible definitionally A, c=1, rstar=2.
ConsumerTarget requires those equalities explicitly (HEq handles the dependent
compatible type) and puts the reference output before quantifying T.

GrowthWitnessTarget is an intermediate conversion for any such constructed
radius. It fixes the original admissible B and positive C₀ and requires a
compact exceptional set for the SAME B, C₀, A, T and R. ConsumerTarget uses
exactly the existential end-growth premise of FiniteTypeTarget and concludes
GrowthAtInfinity A T P.R 1. Weak taming is unnecessary for this bounded geometry;
omitting it strengthens the bounded result, without altering FiniteTypeTarget.
No comparison theorem or full corollary is claimed.

## Pinned meanings and checks

Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612;
FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb.

* Mathlib ContMDiff, mfderiv, TangentSpace and continuous alternating maps
  are the native smooth notions. FsFltz SmoothManifold is a finite-dimensional,
  Hausdorff, second-countable, boundaryless Mathlib manifold. Form and
  exteriorDerivative use those tangent fibers and actual extDeriv in charts;
  pullback uses actual mfderiv. No geometric operation is supplied arbitrarily.
* FsFltz CompactDomain has compact carrier, local regular defining functions,
  and a smooth embedded native boundary with range equal to frontier carrier.
  LiouvilleStructure uses positive contraction dβ(Z,v)=β(v) and outward field.
  Completion.ambient is CompleteLiouvilleManifold with an actual Flow ℝ,
  jointly smooth action and actual chart ODE at every real time. Its original
  primitive, field and full flow are retained without any change of sign.
* Completion includes the smooth extension inclusion, primitive/field
  compatibility, all-real-time endMap defined by the actual flow, embedding
  of the nonnegative cylinder, immersion at every time, exact end_primitive
  exp(t)α(v), coverage by the compact image and nonnegative end, and disjointness
  from the compact image for t>0. The coordinate is LOGARITHMIC: r=exp(t),
  ∂t=r∂r. No compact boundary or inverse coordinate is a new input.
* CylindricalStructure.cylindrical sends (v,s) to
  (contactJ v+s Reeb,−α(v)) through the actual derivative of endMap.
  Reeb normalization is α(Reeb)=1; its dα contraction is zero.
  Together with compatibility this is the manuscript J(r∂r)=Reeb sign.
* CompatibleStructure.g is native ContMDiffRiemannianMetric and metric_eq
  fixes g(v,w)=dβ(v,Jw). MetricTangent has the norm from this g.toCore,
  not the default tangent chart norm. covector transfers the SAME linear map
  using finite-dimensional continuity. dualNorm is its g-dual operator norm.
  inverseNorm is the norm of the inverse positive contraction for dλ from
  that g-dual to that g-tangent. A is unchanged throughout.
* AdmissibleGrowth 1 is smooth on the closed half-line, positive, dominates r,
  and has literal divergent interval integral of r/B(r)^2. GrowthAtInfinity
  has an actual compact-set exception, not an eventual scalar substitute.

## Four-stage reuse inspection and intended construction

1. Pinned Mathlib supplies LocalDiffeomorph and its native inverse-function
   machinery, smoothTransition with exact endpoint values and bounds,
   compact products/images, native proper-map compact-preimage criteria,
   derivative chain rules and real inner-product duality. No Completion
   specific radius theorem was found there.
2. Pinned FsFltz CompletionCollar proves endMap injectivity and local
   diffeomorphism via its imports, then constructs escapingBasin,
   endCoordinates, contMDiff_endCoordinates and endDiffeomorph. These have
   no additional hypotheses. CompletionCollarExtension proves
   CompactDomain.isCompact_boundary from compact frontier and the embedding,
   and endMap_mem_compact_iff (time≤0). These bridge exactly the original
   Completion; they include empty/zero-dimensional boundary cases.
   They do not supply a radial exhaustion or the desired dual norm identity.
3. Inspected the read-only cluster-skeleton snapshot
   2c239b0c03922a1549f18ee3a45a8e0ca25bb28c under
   /var/lib/archon-worker/imports/project-reference/archon_liouville.
   ClusterSkeleton/GeometryTarget.lean LiouvilleData retains the actual
   CompleteLiouvilleFlow and positive sign. It supplies no general cylindrical
   RadialReference construction or GrowthAtInfinity conversion.
4. New infrastructure will only glue a scalar cutoff through the proved
   smooth end coordinates and prove the remaining metric/growth identities.
   A suitable scalar profile is 1+χ(r)(r−1), χ(r)=smoothTransition(2r−3):
   constant 1 for r≤3/2, equal r for r≥2, and between 1 and 2 on 1≤r≤2.
   Set R=1 on the compact domain and use this profile on the positive end.
   Constancy across an open collar proves smooth gluing. Truncations are
   contained in the compact image union the image of boundary×[0,a], hence
   compactness and properness follow by native closed-set arguments.
   The cutoff for growth is at least max(t₀,log 2); B itself is unchanged.

No extra dimension, nonempty-boundary or metric completeness assumption may
be introduced. An interface defect must be reported, not repaired by changing
Statement.lean or upstream. Semantic changes require renewed independent review.
