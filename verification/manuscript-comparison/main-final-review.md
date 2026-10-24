# Independent final mathematical review: general radial comparison

**Verdict: ACCEPT the bounded general radial comparison assembly. No blocking findings.**

Reviewer: independent native reviewer `/root/final_review`, 2026-10-24.
Mission: `92dedb29-ffc9-40f9-8d8c-07db9fc6ffbe`.
Rubric: `$HORIZON_SKILLS_DIR/subagents/reviewers/mathematical-fidelity.md`,
“The Exacting Mathematician”. This is a source-bound mathematical/proof review,
not a formal PR review or full-objective acceptance.

The accepted actual exports are `MainComparison.mainTarget`,
`MainComparison.remainingPaths`, and `MainComparison.comparisonWitness`, with
all 31 source declarations in their three new modules. The first export proves
the unchanged `MainTarget`; it is not merely a definition of a target proposition.
This review excludes the finite-type, Stein, and common-reference corollaries,
full manuscript acceptance, final release packaging/PDFs, and GitHub upload.

## Exact source binding

Reviewed final private commit: `55493c9ba47cc09071f6abf0b16b901a95f19b1f`, repository
`31e09b7d-6080-4383-8e4e-92b14780690a`. The parent supplies verified publication
`c2ebcdf9-664e-4e40-ac92-95c1a88e5d8d`, branch
`horizon/changes/cf79004b-1794-4706-b989-e467e694655a`, and proof-source parent
`64807081e34444a7a0449e4929841852892e3f0c`. I did not repeat publication or claim
independent service-level verification of those publication metadata.

The final commit is absent from local Git. I independently fetched the 25
specific files listed below through the authenticated exact-commit repository
file API, decoded the returned blobs, and compared their complete bytes with
the reviewed workspace files. Every comparison matched. This includes all new
proofs and their frozen statement, original geometry/target/manuscript,
verification drivers, retained reviews, final receipt and all three raw logs.
The committed receipt binds all 307 source files: I recomputed every source
hash, with no mismatch. All 203 imported bindings, five frozen-statement hashes,
and 71 exported elaborated-type hashes also match. I compared all 267 baseline
files against immutable local baseline `f8b5b6bcb56a18c0094d15fed4619ff100327e30`;
none differs. This avoids attributing local HEAD to the final remote commit.

The independently accepted pre-proof gate in `statement-review.md` is unchanged.
I read and reuse the imported Moser/first-path, third-path, and structural-algebra
final reviews at their bound hashes. Their narrower conclusions are consumed
only where this assembly actually discharges their remaining premises. I did
not independently repeat every internal calculus or ODE proof in those accepted
components. I inspected their applied theorem interfaces and the actual chosen
flow constructions, as well as the new proof bodies in full.

## Mathematical findings

1. **The original theorem and native geometry are retained.** Unfolding
   `mainTarget` gives arbitrary `d`, native `SmoothManifold d`, `RadialReference P`,
   exact symplectic `T`, nonnegative weak taming, and `GrowthAtInfinity`, with
   exactly `ExactComparison M T.primitive P.exactStructure.primitive` as output.
   I compared this with manuscript `thm:main`, radial setup, inverse norm,
   growth and conclusion, and read the actual Geometry/Statement definitions.
   There is no parity restriction, nonempty-manifold premise, affine-chart
   restriction, metric completeness, primitive completeness, or primitive-growth
   bound. Zero dimension, empty manifolds and compact exceptions remain allowed.
   Every admissible B is available; no monotonicity or special growth model is
   substituted. The existential growth witness is unpacked only in `mainTarget`.

2. **The metric and operations are actual geometry.** I inspected pinned FsFltz
   `Smooth.lean`, `Family.lean`, and `Liouville.lean`. The manifold uses native
   charts and smooth structure; tangents are `TangentSpace`; forms are continuous
   alternating-map sections; pullback uses `mfderiv`; exterior derivative uses
   native `extDeriv` with actual chart differentials; equivalences are native
   `Diffeomorph`s. The smooth metric satisfies exactly `g(v,w)=d beta(v,Jw)`.
   `MetricTangent`, `covector_apply`, and `inverseContraction_equation` make the
   g tangent norm, g dual norm, and g-dual-to-g inverse operator norm explicit.
   Chart norms are not substituted. Positive Liouville contraction and negative
   Moser forcing are distinct and correct. No bounded Moser evolution is called
   an all-real complete Liouville flow; that separate pinned structure retains
   `Flow ℝ`, joint smoothness, and the actual ODE at every real time.

3. **The second and fourth paths are literal and applicable.**
   `secondPrimitive` is lambda+((1-u)k(R)+uA(R))beta and `fourthPrimitive` is
   (1+v(A(R)-1))beta. Their evolutions specialize the proved radial interpolation
   construction. `second_applicable` supplies order k<=A, divergence of r*k(r),
   and the original weak differential. `fourth_applicable` supplies 1<=A,
   divergence of r and the zero-form weak differential. The actual k and A,
   including A's dependence on the unrestricted primitive, are retained.
   Neither evolution is a free theorem hypothesis or circular output field.

4. **All smoothness, derivative and equation bridges are proved.**
   `interpolation_affine` is an equality of actual form families for every real
   parameter. `interpolation_family` applies the proved native affine-family
   smoothness theorem. `interpolation_equation` differentiates the actual
   coefficient at fixed x,v and uses the actual inverse-field equation with
   its negative sign. For path three, the delivered primitive parameter
   derivative and field equation give exactly the same Moser contract.
   The invoked interval-family smoothness includes genuine open extensions,
   not merely smooth time slices. `fourth_eq_interpolation` proves its scalar
   identity for all real parameters; second equality is definitional.
   Off-interval symplecticity is never required.

5. **Generic exactness is instantiated with constructed evolutions.**
   `interpolation_exactness`, `third_exactness`, and their specializations pass
   the actual delivered evolutions to `moserExactness`; the first-path theorem
   likewise supplies its proved evolution at the original C,K,B inputs.
   `Evolution` contains genuine native/chart ODEs, two-time inverse/composition
   laws, and a smooth open extension; these are outputs of its existence
   construction. The generic exactness theorem legitimately accepts this data,
   while none survives as an extra input to the final comparison.
   The returned gauge is precisely the literal integral of mu_t(X_t) along
   the identity-start evolution. Its global smoothness, primitive equation and
   exterior equation are all consumed, with no assumed Cartan or interchange
   premise. `remainingPaths` proves the reviewed literal three-path contract.

6. **Endpoint order and gauge signs are correct.** Each forward endpoint Gi
   pulls its terminal primitive back to its initial primitive plus dHi.
   The four endpoint equalities identify these literal forms. `psiWitness`
   composes inverse fourth, inverse third, second, first witnesses, giving
   Psi=G4^-1 composed with G3^-1 composed with G2 composed with G1 and
   Psi*beta=lambda+df. I checked `Diffeomorph.trans` order against the actual
   `Witness.comp` and `Witness.symm` proofs. The explicit f is
   H1(x)+H2(G1 x)-H3(G3^-1(G2(G1 x)))-H4(Psi x).
   `comparisonMap` is precisely Psi^-1 and `comparisonGauge` is -f composed
   with Psi^-1. `comparisonWitness` therefore gives F*lambda=beta+dh and
   F*d lambda=d beta for these exact witnesses.

7. **The isotopy and consumer are the advertised native conclusion.**
   `endpointWitness` uses the constructed endpoint isotopy. Algebraic inversion
   swaps jointly smooth forward/inverse families; pointwise composition proves
   both joint smoothness statements with the correct reversed inverse order.
   This proves the unchanged identity-isotopy predicate, including endpoints,
   without compact support. Pointwise composition instead of manuscript smooth
   concatenation changes the proof method, not `thm:main`. No additional
   simultaneous primitive-path claim is made. `Consumers.nativeConclusion`
   unfolds the actual diffeomorphism, smooth gauge, forward and inverse isotopy,
   and both form equations. Its explicit-witness example checks the final
   inverse map and negative gauge without extra hypotheses.

## Verification and trust

I inspected `verify-main-comparison.py` and both Lean drivers. The audit
enumerates the owned namespace/private declarations from the Lean environment,
including generated declarations, and adds the relevant imported interfaces.
All 31 source declarations are covered by the 71-name environment/interface
inventory. Names, receipt declarations, axiom-map keys and type-file keys agree
exactly. All 71 types have verified hashes and nonelided `pp.all` output.

I reparsed the raw axiom log and obtained exactly the stored 71-entry map.
Its union is only `propext`, `Classical.choice`, `Quot.sound`. In particular,
the actual `mainTarget`, `remainingPaths`, and `comparisonWitness` proofs have
no prohibited transitive axiom. The consumer log independently reports the
same allowed-only closure for `mainTarget` and `nativeConclusion`.
No admission, custom axiom, assumed final flow, or hidden comparison premise
was found in the inspected implementation.

All three serial managed checks (named main-module build, full audit, native
consumers) have `ok=true`, return code zero, `status=passed`, and
`snapshot_verified=true`. Each raw JSON report equals its receipt entry, and
both expected Lean completion markers are present. Their common source key is
`3475c9e3509bf5a6c54e6f4f4301772871c2d26c7454b1e3d7e6d381e07dc59a`.
I verified all installed dependency Git heads against `lake-manifest.json` and
empty tracked diffs. In particular Mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`, FsFltz is
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`, and Lean is 4.34.1.
No build rerun was warranted. This is acceptance of the named theorem and its
import closure with consumers, not a fresh release/default-root build.

The proof guide accurately describes the completed bounded theorem and its
exclusions. The crosswalk retains the independently reviewed pre-proof
specification. Only this review report was written by this reviewer; no source,
dependency, manuscript, verification receipt, or proof was edited. This report
is subsequent to the reviewed commit and is not claimed to be in that commit.

## Exact committed SHA-256 evidence

Every file below was independently matched byte-for-byte to the final commit
through its exact-commit file API. The receipt transitively binds all 307 source
hashes and 71 type hashes, independently recomputed as described above.

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/MainComparison.lean` | `cb00802192436e1c4bd1672bfa6b56814e1a4ae776686598c909f323c992709e` |
| `ExactLiouvilleComparison/MainComparisonStatement.lean` | `050e0fda5b0d0c65a92b5c33ff7383f6022bd607ca19f759d57865c533a548cd` |
| `ExactLiouvilleComparison/RemainingPathExactness.lean` | `817f775ee51d8d43863d9251d8dd01637715565eebecad851ade5af6a4af55cc` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `docs/main-comparison-crosswalk.md` | `0ec21662271a54cd98e8a28611fc27150dceb3f035296f39fa3a35754debfe5d` |
| `docs/main-comparison-proof.md` | `5584ee2573c182e9ae14b7d881f6aa18f599f481e62eef6e8d0c4d5d9c41696b` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `verification/main-comparison/final/receipt.json` | `c06cbc7e33ba97e27650df059d850f2b90b03aa63d684cd47b3dcbd451b3a27c` |
| `verification/main-comparison/final/build.log` | `0de93e9cfbf875e7555b29188b51ff0e068ab79ca5e54fd7f74fc49534be97a3` |
| `verification/main-comparison/final/audit.log` | `a869ad5e21d66837be7f81955a67d555760b36498ed7519a264c2c6d45e4a903` |
| `verification/main-comparison/final/consumers.log` | `073df0121ab38e7174436c5fb133e6a4975351a517056dbfd63518acfb9dbfc0` |
| `verification/main-comparison/final/axioms.json` | `ccaf5833ac0b8f76e66dc18c2496b901c6709744d65595370367cd7a285b837b` |
| `verification/main-comparison/final/source-declarations.json` | `9542d4adf5a6d767a84a6f17526eb5e3d91d25d81d7beed3ea14dafc081bbcdc` |
| `verification/main-comparison/final/names.txt` | `541e7fd0924bb67dd5bb9e157a8513a43cf67b1483f868dd861521ab1b25760c` |
| `verification/main-comparison/statement-review.md` | `c282261a43485f7097c10233b376d0e56ee73d122556cfbce7db5ae1e3180f86` |
| `verification/main-comparison/statement-hashes.json` | `3fb92022f583db84f81b635d6d58b7ff208b5f3929250d2024184a1d4a9e198c` |
| `verification/main-comparison/import-manifest.json` | `cb3f47f95fd7bc627c4a984ebae4865ffed81bba750f57e450699b4b8615c95e` |
| `verification/main-comparison/imported-moser-final-review.txt` | `c16bae67eb2dcfd27949e7a5d200a4c4a826ca246f076647a15f7863da137647` |
| `verification/main-comparison/imported-third-final-review.txt` | `593695e51ceadc978aaea9ef16856a2d61658e2d649e334aa2ac4e9968ef0cdc` |
| `verification/exact-comparison-algebra/final-review.md` | `79e55e251f6ba5f8927364f89b7417cb89e2684f1f9ba1d51fda051a33e75dd1` |
| `verification/main-comparison/Audit.lean` | `57861d115794701da3f5f3b40d7d96ba521c1415f761d6c6a5e353ef1e61b502` |
| `verification/main-comparison/Consumers.lean` | `a3120ec358c7c2423074855133a73a18aa1c6f11df47c64efcda6baf52f7681d` |
| `scripts/verify-main-comparison.py` | `71ca9f110be3edbb0fda86acab2402fa91930f976f3a0bde36e7d22dde3f7fad` |
| `.gitignore` | `290d64d2b3d0ef2026db75b18f29a761b94345fae94694bb0846abefdada67c8` |
