# Independent pre-proof statement and definition review

**ACCEPT for bounded mission 7d0fe0b7-a970-4cef-ae30-6b624452f600, revision 1. No statement repair is required before the bounded application proof.**

Reviewer: independent native agent `/root/assembly_statement_review`, 2026-10-24. I authored no implementation. This verdict accepts the two new specification modules and the definition crosswalk at the hashes below. It does not treat their aliases as proofs, accept future implementation, or certify unrestricted intrinsic source-presentation equivalence or the final project.

I read AGENTS.md, docs/objective.md, the unchanged complete manuscript, the new statement modules and crosswalk, actual Geometry.lean and Statement.lean, and the delivered main, finite-type reference/growth, Stein and common-reference applications. I inspected native Mathlib RiemannianMetric and Flow definitions, pinned FsFltz Smooth/Liouville/FixedAmbient definitions, and the specified cluster-skeleton GeometryTarget LiouvilleData conversion. I reused the source-bound prerequisite final reviews for previously accepted proof internals; I did not redo their complete ODE/calculus proofs.

## Reconstructed statements and mathematical findings

1. `ApplicationTarget` is exactly `FiniteTypeTarget`, with every natural d, actual LiouvilleDomain D, Completion C, and CompatibleStructure A for `completionReference C`; a CylindricalStructure C A; then every ExactSymplecticStructure T. Its only further premises are nonnegative weak taming and existential B, positive C0, nonnegative t0 with the inverse estimate for every boundary y and every t >= t0. B is arbitrary AdmissibleGrowth 1, not a fixed model or a monotone subclass. The conclusion compares T.primitive with the actual C.ambient.primitive. No radius, growth conversion, global Moser flow, comparison conclusion, metric completeness, completeness of T, or primitive-growth estimate is an input.

2. `AssemblyTarget` is exactly `MainTarget ∧ FiniteTypeTarget ∧ SteinTarget ∧ CommonReferenceTarget`. MainTarget quantifies arbitrary d, native boundaryless M, the radial reference and arbitrary exact symplectic T. RadialReference fixes smooth proper R >= 1, c > 0 and rstar > 1, and requires its primitive identity and c times the squared g-dual norm bound only where R > rstar. WeaklyTames is >= 0 for every vector; nondegeneracy is a separate exact-structure field. GrowthAtInfinity has an existential compact exception only for the inverse estimate, preserving the full smooth positive B on its closed half-line and the actual divergent interval-integral limit. No completeness premise appears in MainTarget. The delivered `MainComparison.mainTarget` really proves this type by unpacking growth and applying its constructed endpoint witness.

3. SteinTarget has quantifier order `forall d N M i, exists P : SteinReference i, forall T, ...`. P is an output before T; PackagedSteinTarget alone would not suffice. The delivered SteinComparison.steinTarget supplies the actual embedding-only constructed reference. P fixes J = i.J, beta = -(1/4)dR composed J, R = exp(1) + norm(i.map)^2, and g equal to the induced real Euclidean metric. Stein growth begins at exp(1); the existing extension/compact-enlargement theorem discharges the main input. No finite-type or complete-primitive premise is introduced.

4. CommonReferenceTarget separately quantifies both exact structures, both weak-taming premises and both GrowthAtInfinity premises. Therefore B, C and the compact exception may differ. The existing theorem uses two proved main comparisons. Its explicit consumer gives Phi = F1 composed F2 inverse and q = (h1-h2) composed F2 inverse, with the correct pullback orientation.

5. `CompleteTarget` is exactly CompleteLiouvilleComparisonTarget. It retains CompletePrimitive data for the two prescribed primitives, in addition to the general radial assumptions. FixedAmbient.CompletePrimitive refers to the actual canonical Liouville vector, positive contraction d lambda(Z,v) = lambda(v), and CompleteLiouvilleFlow. That flow is native Flow over all real times, with joint smoothness and the actual chart ODE at every real t. Flow addition and zero laws give inverse maps at negative times. Completion.ambient likewise is an actual CompleteLiouvilleManifold. The general exact-symplectic T is never renamed a complete Liouville manifold. Specializing the main theorem while retaining these data is legitimate; it does not infer primitive completeness or Liouville-field conjugacy from an exact gauge change.

6. NativeConclusion expands ExactComparison without losing content: an actual Diffeomorph F, smooth h, a family H of actual diffeomorphisms with H0 = id and H1 = F, forward and inverse joint ContMDiffOn on [0,1] times M, the literal primitive identity with +dh, and the exterior-derivative identity. The reorder of existential witnesses adds no premise. The expected consumer can unpack the existing conclusion directly; this definition itself is not that consumer proof.

## Exact reference and norm bridges

`FiniteTypeRadial.reference C A cyl` unfolds through constructedRadius and Radius.toReference. Its exactStructure is literally completionReference C, whose primitive is C.ambient.primitive; its compatible field is literally A; its R is the constructed radius; c = 1 and rstar = 2. Consequently J, the metric inner product, MetricTangent norm, covector transfer, dualNorm and inverseNorm are definitionally unchanged. Reflexive equality lemmas and the reflexive weak-taming iff are appropriate bridges. They must still be delivered as the promised consumer interface.

Geometry.CompatibleStructure.metric_eq fixes g(v,w) = d beta(v,Jw). Its native smooth Riemannian metric has positive-definite symmetric inner products; MetricTangent installs the associated norm on the same underlying vector space. Covector conversion preserves linear values and uses finite dimension for continuity. InverseContraction is constructed from nondegeneracy, finite-dimensional bijectivity and positive contraction; inverseContraction_equation verifies its meaning. inverseNorm is exactly the operator norm from g-dual to g-tangent. There is no chart-norm substitution or free inverse operation.

The existing `reference_growth` accepts exactly the FiniteTypeTarget growth premise. growth_witness uses the complement of farEnd at max(t0, log 2), proves it compact and substitutes the proved R(endMap(y,t)) = exp(t). It keeps the same B and C0. The independently accepted finite-type construction supplies smoothness, properness, lower bound, the compact-core bound and both radial identities; none becomes an application hypothesis. The planned main-theorem application therefore has no uncovered geometric premise.

## Native definitions and source-presentation boundary

FsFltz SmoothManifold packages native Hausdorff second-countable boundaryless Mathlib manifolds with Euclidean real model. Tangent is native TangentSpace; Form is a section of continuous alternating maps; scalarDerivative and pullback use mfderiv; exteriorDerivative uses native extDeriv of chart coefficients transported by actual chart differentials; SmoothEquiv is native Diffeomorph. The inspected cluster LiouvilleData conversion retains the same manifold, primitive, vector and complete flow, so it supplies no missing comparison application. Reusing the existing general interfaces is appropriate.

The crosswalk states a real coverage boundary, and I independently confirm it. Completion is an explicit realization: a compact regular-sublevel domain in a boundaryless extension, a smooth boundary embedding, a smooth inclusion of the extension, an actual complete ambient primitive, and a complete-flow end with embedding/immersion, exp(t) alpha identity, covering and overlap. The target is universal over such realizations. It does not construct a realization from every separately defined intrinsic manifold-with-boundary completion. The all-real end conditions are meaningful for the existing complete flow, not assumed Moser evolutions. CylindricalStructure imposes the manuscript's prescribed end J formula; compatibility of A supplies the compatible metric. Existence/extension of such a cylindrical J from an arbitrary domain is not proved by this target.

ProperComplexEmbedding records actual smooth proper topological embedding plus injective derivative and the real Cauchy–Riemann equation for a smooth J with J squared = -id. These are genuine geometric data and are enough for the constructed Stein argument; no symplectic/radial/comparison conclusion is hidden in the input. Nevertheless no Lean conversion from a separately packaged complex-manifold holomorphic embedding was inspected or supplied. Thus the formal target covers this explicit native real presentation, rather than establishing its equivalence to every intrinsic holomorphic presentation. This boundary is already stated clearly in the crosswalk and is not a blocker for proving the unchanged bounded targets. Final claims of full intrinsic manuscript coverage require root's explicit resolution; this review does not silently waive that obligation. The source also states existence of compatible cylindrical J, which is outside this assembly.

## Verification and preservation

I did not run a concurrent build. The provided managed log records an initial out-of-date check followed by actual builds of both new statement modules and a final successful 3824-job build. The final managed receipt reports returncode 0, snapshot_verified true and source key `17851a211ad691d4d8a8dc11fe2b55b8f5b95af70415768ed861cae7e77ab738`, Lean 4.34.1. This establishes compilability of the reviewed specification/import assembly, not a proof of its aliases.

I independently recomputed all 645 expanded manuscript import-manifest entries and all 108 corollary import-manifest entries: no mismatch. All 312 finite-type receipt source bindings, all 18 metric-child source bindings, all 11 metric-child dependency bindings (resolved relative to .lake/packages), and all 326 corollary receipt source bindings, and all 307 main-comparison receipt source bindings match. Dependency HEADs equal FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The earlier source-bound reviews and receipts are suitable evidence for using these accepted prerequisites in a bounded application. This pre-proof review does not replace the required final elaborated-type and transitive axiom audits of the forthcoming theorem terms.

The only file written by this reviewer is this report. No authoritative source, accepted prerequisite, dependency, implementation or statement was changed. No remote publication was performed.

## SHA-256 binding

| Artifact | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/FiniteTypeComparisonStatement.lean` | `27a6e4b9757f15bc68e86ad9fa701b10ecd9d2169c762d4dfe1bde64637c9513` |
| `ExactLiouvilleComparison/ManuscriptComparisonStatement.lean` | `cb0d42d1b903b5d0a05192dbcf09548866631216d9c4db718fc8f3ae0aa4a473` |
| `docs/manuscript-comparison-crosswalk.md` | `eb12808878aba21724d3bee77ee11274c97a3198d00ae70285d63fad86632344` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `ExactLiouvilleComparison/MainComparison.lean` | `cb00802192436e1c4bd1672bfa6b56814e1a4ae776686598c909f323c992709e` |
| `ExactLiouvilleComparison/FiniteTypeRadial.lean` | `7fcb1922ebcc46d5884ef636a4ab679e65615d69be5a3ef491c6a17d8809ba64` |
| `ExactLiouvilleComparison/FiniteTypeRadialGrowth.lean` | `43766cb4b0efdaec288ce02ca8bf8e27dca185018a8a44c71125ee2f5ffd776f` |
| `ExactLiouvilleComparison/SteinComparison.lean` | `6f1cf4fab120e3dfd1822f52776e147c02787c6472c3bc5b4c13dc739da3feb6` |
| `ExactLiouvilleComparison/CommonReferenceComparison.lean` | `163666997ab72a8595036234277101af1b44bb82d020f8c3eae2ca46c8918656` |
| `verification/manuscript-comparison/import-manifest.json` | `1e70d0ee240ba45daf0871edd6b118b7dadf1889951fe68d14c427114d05d29e` |
| `verification/corollaries/import-manifest.json` | `eb72774c4b4c89dee03dd5ae995cc415c9f62a1ce42a2de57f22169939d937b3` |
| `verification/finite-type-radial/receipt.json` | `6bed8981b1a0833418c6fdc3d91a923dd0e1b6a584bd1d3be5443523230acc06` |
| `verification/finite-type-radial/final-review.md` | `914a676d4e61a991cbccb5a54170887f2e8db01ba44ac7f2f167caae5a666617` |
| `verification/finite-type-radial-metric/receipt.json` | `1ec30d6edfa416b1bb542010331de78bae013b974bc40782216f154cac4dc0bd` |
| `verification/finite-type-radial-metric/final-review.md` | `e9f459b1da25ce98c1dc4b1b39829d164880c4b41807544f0dd17a7ea77c93c1` |
| `verification/corollaries/final/receipt.json` | `933f0d9843eaa5fd408c9872ce7ec95ff0a9cfa9d35a999e3bbbdf7439feea17` |
| `verification/manuscript-comparison/main-final-review.md` | `665575c38af27592719cd5a7eaa10acad408c4ded3fd2837f426e4b77954c2ff` |
| `verification/manuscript-comparison/corollaries-final-review.md` | `7654ec7b6f878c8fad6e0f5b7fd4378ff3002163faa2f384aa0c7f9d89d4cf8f` |
| `lake-manifest.json` | `2790d3bafa974c7cbdd6e9ca85ac8e33d1caf801ab00d645ceebaea8aa65ba83` |
| `lean-toolchain` | `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Liouville.lean` | `d51b04337e39b31ab1b1d3b20093ba5956b8ea0b04456e141ef4c827268b335e` |
| `.lake/packages/fsfltz/FsFltz/Geometry/FixedAmbient.lean` | `8fcedb064de005c2d236a425cebcbd0dfc137c8f102070592cb5eef9efb60d16` |
| `/var/lib/archon-worker/scratch/7be0908b-3d0b-4181-ac32-a385803c33d2/assembly-statement-build.log` | `4d1352d702ebbcaf5a8fce75074d2c686dad875ea0a8220c28442f4e270cc48b` |
| `verification/manuscript-comparison/main-receipt.json` | `c06cbc7e33ba97e27650df059d850f2b90b03aa63d684cd47b3dcbd451b3a27c` |
| `verification/manuscript-comparison/statement-build.log` | `4d1352d702ebbcaf5a8fce75074d2c686dad875ea0a8220c28442f4e270cc48b` |
