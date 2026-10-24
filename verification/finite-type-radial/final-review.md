# Independent final source-bound review: finite-type radial reference

**Verdict: PASS for bounded mission `9329795b-7d27-46a3-adb3-79b3711aaf56`. No blocking finding or semantic repair required.**

Date: 2026-10-24. Reviewer: independently delegated agent `/root/finite_type_final_review`, which authored none of the reviewed semantic or proof source. This report renews the statement and definition assessment for the actual implementation and accepts its bounded construction, exact metric identities, growth conversion, and consumers. It does not accept `FiniteTypeTarget`, `MainTarget`, the full manuscript, or a project phase.

## Exact source and evidence boundary

The reviewed private implementation is commit `9acd2ca5be07c490e1d9d48ac3e938390ac9a987` in repository `31e09b7d-6080-4383-8e4e-92b14780690a`, branch `horizon/changes/55d29ac6-904d-4934-979d-3aab109eefb3`. Its parent is the metric child final delivery `9716da2fdab7d268cfea6fbc3808a40cf3a47546`.

I inspected `/tmp/finite-type-final-delivery.json`, `/tmp/finite-type-final-change.json`, and `/tmp/finite-type-final-uploads.json`. Publication `b39f54d0-502c-4cae-96fc-9a94fe0055c4`, operation `55d29ac6-904d-4934-979d-3aab109eefb3`, records `git_tree_delta` verification of the exact requested file operations, commit parent, and preservation of unchanged tree entries at 2026-10-23T22:56:05.335340+00:00. I independently checked that all 25 uploaded files match the local reviewed bytes in both SHA-256 and byte length; artifact IDs match each requested operation; and upload, operation, and verified changed-path sets coincide. The publication receipt explicitly excludes Lean validation; that is supplied separately below. I did not perform a new remote readback.

I read AGENTS.md, docs/objective.md, the authoritative manuscript's finite-type setup and `cor:liouville`, the independent pre-proof statement review, the crosswalk, the proof guide, all eight combined Lean modules, and the original Statement.lean, Geometry.lean and relevant LinearAlgebra.lean metric declarations. I inspected actual pinned FsFltz/Mathlib definitions and proof bridges for end coordinates, local diffeomorphisms, compact boundary, closed end rays, native differential forms and derivatives, complete flows, the native integral-curve bridge, and smoothTransition. I also read the metric child's independent final review.

All 312 entries of the combined receipt's source/dependency manifest match the inspected workspace. All 267 preserved baseline entries match. The metric child's 18 source and 11 dependency bindings match; its retained final review and receipt are also bound by the combined receipt. Every locally available file bound in the pre-proof statement review remains unchanged. In particular, FiniteTypeRadialStatement.lean and its crosswalk retain their accepted bytes, and the original Statement.lean, Geometry.lean, and authoritative manuscript were not edited. Both dependency HEADs equal their pins and their tracked Lean-file diffs are empty.

This review used read-only inspection and independent byte/inventory checks, relying on the exact passed managed Lean receipts rather than launching a competing build. Its only authored file is this report. The report is intended for a documentation-only descendant of the reviewed implementation.

## Renewed statement and definition assessment

The implementation faithfully proves the previously reviewed specification. `constructionTarget : ConstructionTarget`, `growthWitnessTarget : GrowthWitnessTarget`, and `consumerTarget : ConsumerTarget` are actual theorems. Their fully elaborated types contain exactly those propositions, with no additional section variables or hidden premises. `constructedRadius` builds every Radius field from arbitrary natural dimension d, the original LiouvilleDomain D, Completion C, compatible structure A, and CylindricalStructure C A. Neither a radius nor its smoothness, properness, metric identities, a Moser flow, MainTarget, or an exact comparison is an input to that construction.

The reference is produced before T and its growth data are quantified. It has definitionally the original completionReference C, primitive, A, J and g, with c=1 and rstar=2. The end equality includes exp(t)=2; the identities are required where R>2; the complementary strict-end cutoff is compact and has R≤2. These are precisely the geometric choices used in manuscript lines 402–407. The consumers expose the preserved exactStructure, compatible structure, primitive, J, g, R and constants as equalities, rather than permitting an unspecified replacement reference.

The actual geometry is retained. SmoothManifold uses native boundaryless Mathlib charts and IsManifold, native tangent spaces and continuous alternating forms. Its exterior derivative is the actual chart extDeriv transported by chart derivatives, and scalarDerivative is mfderiv. The reference metric is a native smooth Riemannian metric explicitly fixed by g(v,w)=dβ(v,Jw). MetricTangent's norm comes from this metric's core; the LinearAlgebra inner-product instance uses that same core. The covector conversion preserves its linear values, dualNorm is its operator norm on the g-tangent, and inverseNorm is the norm of the proved inverse positive contraction from g-dual to g-tangent. No chart norm is substituted for either metric norm.

The complete Liouville terminology and sign remain correct: Completion.ambient contains CompleteLiouvilleManifold with the actual primitive, field, positive contraction dβ(Z,v)=β(v), and CompleteLiouvilleFlow. The latter contains Flow ℝ, joint smoothness, and the chart ODE at every real time. The native Flow has addition and zero laws, so negative times are present as actual inverse maps. End_flow identifies endMap with this same flow. The new T remains ExactSymplecticStructure and is not required to have complete primitive flow. No completeness is inferred from an exact gauge change.

All natural dimensions are retained. The pinned endMap local-diffeomorphism proof explicitly handles d=0 using CompactDomain.zero_boundary; other dimensions use native immersion and equal finite ranks. The new compactness, gluing and growth arguments require neither positive dimension nor a nonempty boundary. The empty-boundary case is covered by the original compact-image covering. There is no metric-completeness hypothesis, monotonicity assumption on B, restriction to a special B, or primitive-growth assumption. Weak taming is unnecessary for this bounded geometric conversion and remains unchanged in the original FiniteTypeTarget.

## Proof inspection

1. **Actual radius and smooth gluing.** The profile `1 + smoothTransition(2*r-3)*(r-1)` is proved smooth, ≥1, equal to 1 for r≤3/2, equal to r for r≥2, and ≤2 for r≤2. The radius is its value on exp(t) using the proved inverse end coordinates on the escaping basin, and 1 off that basin. `radius_end` proves the formula for every real end time from the inverse equations. At basin points, smoothness follows from the native smooth local inverse and eventual equality. Off the basin, the complement of the closed end ray starting at log(3/2) is a genuine open neighborhood on which the function is constant. The imported closed-ray theorem is itself proved from the compact inclusion's open interior complement and the actual complete flow's homeomorphism; no new gluing or regularity assumption is introduced.

2. **Compact remainder and properness.** The strict end beyond any real a is open. Its complement is a closed subset of the compact domain image union the image of boundary×[0,a], using the original covering. Boundary compactness is proved upstream from its embedding onto the frontier of the compact carrier. This containment also works for negative a. Closed sublevels R≤b lie in the compact complement of the end beyond log(max(2,b)), since R=exp(t)>b on that tail. The native compact-preimage criterion then proves IsProperMap for R. The separate core-bound proof gives R≤2 off the strict end t>log(2), so every point needing a radial identity has actual end coordinates with t>log(2).

3. **Native differential and exact metric calculation.** The metric child's source was retained unchanged and its hypotheses are discharged by the newly constructed radius. The derivative theorem first proves equality on an open neighborhood where exp(t)>2 and then applies native germ equality and the manifold chain rule, obtaining dR(d endMap(v,s))=exp(t)*s. It does not differentiate a lone pointwise equality. Derivative surjectivity follows from the actual end local diffeomorphism. Differentiating end_flow and applying the proved complete-flow integral-curve bridge gives d endMap(0,1)=Z for the original field. Cylindrical J, the derivative formula, and end_primitive therefore prove β=−dR∘J for every ambient tangent vector. Positive contraction, J²=−1 and the original metric give g(Z,w)=dR(w). Native Riesz duality identifies the same transferred covector with the Riesz image of Z, yielding exactly |dR|²_(g dual)=g(Z,Z)=dR(Z)=exp(t)=R. No gradient or norm conclusion is assumed.

4. **Packing and unchanged growth witnesses.** Radius.toReference supplies the actual original reference and derives its radial inequality from the stronger dual-square equality. `growth_witness` chooses K as the complement of the strict end beyond max(t₀,log(2)). That set is proved compact. Outside K, the original estimate applies at t≥t₀ and Q.R=exp(t), so the same B and C₀ transfer without any change. The stronger intermediate lemma needs neither positivity of C₀ nor t₀≥0; the advertised target retains these source premises. `growth` packages the original admissible B and positive C₀ into GrowthAtInfinity. `reference_growth` applies it to the radius actually constructed here, and consumerTarget produces the reference before the T quantifier.

5. **Consumers and absence of circularity.** FiniteTypeRadialConsumers checks all three specification proofs, the exact reference-data equalities, the native derivative at the constructed R, and the fixed-B/C₀ growth conversion. The metric consumers expose both radius-coordinate equality and the literal c=1 radial fields. Reading the proof dependency chain shows geometric construction followed by its consumers; the output Radius is not silently assumed by constructionTarget. There is no arbitrary geometric operation, assumed comparison or Moser evolution, circular field, sorry, admit, custom axiom, or unverified opaque proof in the accepted dependency chain.

## Managed verification and transitive audit

The combined verification script performs preservation/pin checks, builds FiniteTypeRadialConsumers (importing all eight modules), and runs Audit.lean. I inspected both source programs and the raw logs. Both managed checks have returncode 0, ok=true, status=passed and snapshot_verified=true at the same source key:

`67617b8b6dadf88867ea5dde583c25bbaa52d86cf690b36503b64991e06586c8`.

The parsed final JSON records in final-build.txt and final-audit.txt exactly equal the receipt entries. The build log initially reports an out-of-date target during its managed check, then rebuilds FiniteTypeRadial and FiniteTypeRadialConsumers and ends successfully. This is not an unresolved build failure, and I do not represent the cached dependency build as a fresh uncached rebuild. The audit log contains its completion marker. The toolchain is Lean 4.34.1; FsFltz is pinned to `1a3d387cfacc746e25aad31e5b27b1803103e7cb`, Mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Audit.lean enumerates both owned namespaces, including generated/private-prefix declarations, pretty-prints their actual types with universes, full names, explicit arguments, proofs and deep terms enabled, and calls Lean.collectAxioms on every declaration. I verified that the 59 source declarations are all present in the 95-name environment inventory, that its name set equals the axiom-audit keys, and that every transitive axiom set is a subset of {propext, Classical.choice, Quot.sound}. This includes the actual constructionTarget, consumerTarget, intermediate proofs and consumers; it is not merely an audit of proposition definitions.

The full gzip inventory decompresses to exactly 3,839,192 UTF-8 bytes, SHA-256 `4863218a235959aae0dfe0d339c83071c58471637f2c34896f76a58491c5f30f`, matching the receipt. Its 95 top-level declaration headers match the environment inventory exactly, with no omitted `⋯` placeholder. I inspected the advertised theorem types and sampled the dependent construction/consumer types against their source. The separate readable inventory aids inspection. The earlier statement inventory decompresses to 1,447,628 bytes, SHA-256 `792a79274a4fa381925ee1f60347286ad1a6aae764b6d93c4e292209a37f4fc6`, exactly the bytes bound by the pre-proof review. Its earlier default proof display is superseded by the final full audit; compression changes no Lean statement.

## Acceptance boundary

The bounded mission is accepted: an actual smooth proper R≥1 with the specified end equality and compact remainder has been constructed; the original primitive/J/g identities and c=1, rstar=2 radial reference are proved; the end-growth premise is transferred with unchanged witnesses; and all advertised consumers pass the exact-source managed checks and transitive axiom audit. The independent pre-proof specification and definition crosswalk remain applicable, now with their output obligations proved.

This supplies the radial-reference construction and growth conversion in the proof of cor:liouville. Applying the main comparison theorem and constructing the manuscript's diffeomorphism, isotopy and exact potential remain outside this bounded delivery. No full corollary, MainTarget, ManuscriptTarget, final standalone packaging, PDF completion, GitHub upload, or full objective/phase acceptance is claimed. The proof guide states that boundary accurately. I also inspected docs/finite-type-radial-delivery.md: its implementation identifiers, radial-reference facts, exact managed-check facts, and retained comparison boundary are consistent with this review. `constructed_growth_witness` specifically requires importing FiniteTypeRadialConsumers; it is not declared in the base FiniteTypeRadial module. Administrative ownership identifiers and superseded-run history in that handoff are not additional mathematical acceptance claims.

## SHA-256 bindings

The bound combined receipt contains the full 312-entry source/dependency manifest. The following additional explicit bindings identify the reviewed implementation and evidence; paths are relative to the workspace unless absolute.

| File | SHA-256 |
| --- | --- |
| `AGENTS.md` | `779b846ce732d3f81e859d536d7f31e4354a1650ace887d37e68c3b36abf654a` |
| `docs/objective.md` | `0f7ca4a2449cca3d400e7afda913364582be71f858fe31475fa60665502ce5e8` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/FiniteTypeRadialStatement.lean` | `5c628a902112976da8252a44f55801395c715526b11e3bfe362fbdbfbb200daa` |
| `ExactLiouvilleComparison/FiniteTypeRadialRadius.lean` | `b24155e38d6bc774ffbcf5c4a92950b7d3695a6a11e4af03718d593c570ab875` |
| `ExactLiouvilleComparison/FiniteTypeRadialGrowth.lean` | `43766cb4b0efdaec288ce02ca8bf8e27dca185018a8a44c71125ee2f5ffd776f` |
| `ExactLiouvilleComparison/FiniteTypeRadialMetricStatement.lean` | `19e07aded10817181abdf3b74effff7c29a2f3dd1dda6e2c45e8dbfb1356cbad` |
| `ExactLiouvilleComparison/FiniteTypeRadialMetric.lean` | `de6919a3c85f40318c71007472b3dcb63749df9d1f8f9afaefc549249a50424d` |
| `ExactLiouvilleComparison/FiniteTypeRadialMetricChecks.lean` | `5223aff14359cd5d20c05b4551cccc8ef7231aa4d436dfd297fadc38fd86fd06` |
| `ExactLiouvilleComparison/FiniteTypeRadial.lean` | `7fcb1922ebcc46d5884ef636a4ab679e65615d69be5a3ef491c6a17d8809ba64` |
| `ExactLiouvilleComparison/FiniteTypeRadialConsumers.lean` | `42f7984aaf839d351584f610acaa9cb6b4c279295781995be3ec6d60d8cf13ca` |
| `docs/finite-type-radial-crosswalk.md` | `291daffcb519975c8db5c1b7875bbe72e7f4d05024e576a386a2a435424f42fc` |
| `docs/finite-type-radial-proof-guide.md` | `b7c1fdf8f6ac976ab99f7dc8214ff3daa10c87c90a2a3a04b8df6b2347f85fb0` |
| `scripts/verify-finite-type-radial.py` | `6dd3ffd09c5b186fc48ef3095bc91a5a3f0155e6a08308f216ab8790565cae64` |
| `verification/finite-type-radial/statement-review.md` | `200c2f8c5221fd578ce7b646c5fab9fed436ceafc02203be6fdc8199fe612c6f` |
| `verification/finite-type-radial-metric/final-review.md` | `e9f459b1da25ce98c1dc4b1b39829d164880c4b41807544f0dd17a7ea77c93c1` |
| `verification/finite-type-radial/receipt.json` | `6bed8981b1a0833418c6fdc3d91a923dd0e1b6a584bd1d3be5443523230acc06` |
| `verification/finite-type-radial/Audit.lean` | `66ba9841ac30a120f16ad6dfbf70cb144f6470104908eef348e71c8d586f4d94` |
| `verification/finite-type-radial/axiom-audit.json` | `387ccd8735661e4a6b22044bd1bc84c35379d5ba25d6d14db673614c1926bf19` |
| `verification/finite-type-radial/declarations.json` | `6b19977bc3bf3e1be3c85e5b319c36034e3bafffff29ab0c23c5b87e3cfce1d6` |
| `verification/finite-type-radial/environment-declarations.json` | `9d3815b59adcfc94162d79ba2b96e5af14b7d59c8df761277462be5952af24db` |
| `verification/finite-type-radial/elaborated-types-full.txt.gz` | `c541777d289419ec2c6ab2aa12ad44b2179e857517dc577c65068291b7413a29` |
| `verification/finite-type-radial/elaborated-types.txt` | `fa510b3c11013c9c9dd2b4be44afcd78b63a55b2b441313ddaae4a86bdc848a2` |
| `verification/finite-type-radial/statement-inventory.types.gz` | `468d55139fdac1528d4e8f94edd5e47d4f2ccf3efa93f0c7350fb5cba88ad734` |
| `verification/finite-type-radial/final-build.txt` | `9581b21e92adc50c0eb6715a61f147f5c164406e43b235aab8996d9dd3179205` |
| `verification/finite-type-radial/final-audit.txt` | `3b52eda9b2a1e74525261858a0b4e40302405155f93f81e4d117e9d3cd3998de` |
| `/tmp/finite-type-final-delivery.json` | `8f929a3552668268778bc050f61a7d4bff924c19bd69201a465af38f3544b39f` |
| `/tmp/finite-type-final-change.json` | `704aae9189d19a9dfa18ad2b894c4a6b8e1dd2363c58665ab8fa39092e794e0e` |
| `/tmp/finite-type-final-uploads.json` | `a788f7f3c16804de4384810a8bc0504b406fc5e15e1baf6b47aee00c214e30b3` |
| `docs/finite-type-radial-delivery.md` (documentation-only handoff) | `b33bd43d708cfd9fe7d67676c2034059d016570f10d8e00050e142f7d6d63f0e` |
