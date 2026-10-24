# Finite-type application and manuscript assembly

Import `ExactLiouvilleComparison.ManuscriptComparison`. The new actual proofs
are `FiniteTypeComparison.finiteTypeTarget : FiniteTypeTarget`,
`ManuscriptComparison.manuscriptTarget : ManuscriptTarget`, and
`ManuscriptComparison.completeLiouvilleComparisonTarget : CompleteLiouvilleComparisonTarget`.
These inhabit the unchanged propositions in Statement.lean. The statement
module alone is not proof evidence. This bounded delivery does not perform
phase acceptance, final project packaging or GitHub upload.

## Application and exact transports

`finiteTypeTarget` introduces precisely the original d, LiouvilleDomain D,
Completion C, CompatibleStructure A, CylindricalStructure, target exact
symplectic structure, weak taming, and existential eventual end-growth premise.
It applies the delivered MainComparison.mainTarget to
FiniteTypeRadial.reference C A cyl. The delivered reference_growth constructs
the compact exception and transfers the same growth witnesses. No radial
exhaustion, metric bound, metric completeness, Moser flow or comparison is
assumed by the application.

The reference has c=1 and rstar=2. Its exactStructure is completionReference C,
compatible is A, and primitive is C.ambient.primitive by definitional equality.
The new reference_exactStructure/reference_compatible/reference_primitive and
reference_constants lemmas expose those facts. reference_inner, reference_dualNorm,
reference_inverseNorm and reference_weaklyTames_iff make the norm/taming transports
explicit. Therefore the main theorem's inputs and output elaborate at the
original objects without any transported replacement metric.

The constructed main witness supplies the diffeomorphism F, smooth gauge h,
F*lambda=beta+dh and F*d lambda=d beta. native_of_exactComparison merely unpacks
the already proved witnesses; nativeConclusion exposes the actual identity-start
isotopy H and both joint forward/inverse smoothness conditions on [0,1].
ManuscriptComparisonConsumers.finiteTypeNative writes these conclusions out
literally at C.ambient.primitive and its actual exterior derivative.

## Assembly and complete terminology

`manuscriptTarget` combines four proof terms, not four target declarations:
MainComparison.mainTarget, FiniteTypeComparison.finiteTypeTarget,
SteinComparison.steinTarget, CommonReferenceComparison.commonReferenceTarget.
The Stein term constructs the reference from the embedding before quantifying
the target primitive. It is the source-level SteinTarget, not merely the packaged
conditional version. The imported CorollaryComparisonConsumers expose the
literal Stein primitive/induced metric and common-reference Phi and q.

`completeLiouvilleComparisonTarget` specializes the general theorem with the
original two CompletePrimitive arguments in its type. Their actual all-real
smooth flows remain attached to those prescribed primitives. The consumer
prescribedFlow exposes their unchanged flow, positive contraction and coordinate
ODE for every real time; completeNative combines unchanged flow identities with
the actual native comparison. No completeness is inferred from an exact gauge,
and neither completeness nor finite type is added to MainTarget.

## Source coverage and trust boundary

The independently reviewed `manuscript-comparison-crosswalk.md` maps thm:main,
cor:liouville, cor:stein and cor:two, including native operations and the explicit
g tangent, dual and inverse operator norms. It records the presentation limits:
FsFltz Completion is an explicit completion realization; the embedding input is
native real Cauchy–Riemann data. Intrinsic completion-presentation equivalence,
conversion from Mathlib complex holomorphic embeddings, and existence of a
chosen cylindrical J are not newly proved here. These limits are reported for
root's broader source-presentation acceptance; no target was corrected or criterion
removed. All four unchanged formal targets are the assembly obligation.

Exact private prerequisite commits, source hashes and review bindings are in
verification/manuscript-comparison/import-manifest.json and
prerequisite-bindings.json. The main and Stein/common independent reviews are
retained here, and the finite radial review remains in its original directory.
All accepted semantic files, baseline files, manuscript and dependency pins are
preserved. No upstream or cluster-skeleton file was edited.

## Reproduce the bounded validation

Run `python scripts/verify-manuscript-comparison.py` in the managed Lean
environment. It verifies baseline/statement/import/review source bindings and
actual dependency pins, then serially builds the consumer module, runs Audit.lean,
and elaborates the consumer source. Accepted checks require snapshot_verified=true
and a common source key. Existing managed caches are reused.

Audit.lean inventories every declaration in the new namespaces, the four actual
prerequisite/application target proofs, the exact target propositions, metric
and growth definitions, native form/differential/pullback/flow definitions and
structure constructors exposing their full fields. It emits nonelided fully
explicit elaborated types and relevant definition bodies. Each declaration gets
a transitive Lean.collectAxioms audit allowing only propext, Classical.choice and
Quot.sound. Compressed large files retain uncompressed byte counts and hashes.
The receipt under final/ binds sources and validation outputs; independent final
review and the private delivery record bind those exact bytes to a committed tree.
Inherited receipts retain their own source keys, not the combined tree's key.
