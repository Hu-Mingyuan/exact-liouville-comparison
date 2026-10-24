# Independent finite-type radial statement review

Date: 2026-10-24. Mission: 9329795b-7d27-46a3-adb3-79b3711aaf56, revision 1.
Reviewer: independently delegated statement-review agent `/root/finite_type_statement_review`; the reviewer authored no semantic or proof source for this module.
Baseline: `f8b5b6bcb56a18c0094d15fed4619ff100327e30`.

**Verdict: PASS for the bounded specification and definition crosswalk. No blocking semantic finding.** This is a pre-proof statement review only. It accepts neither a proof of the three target propositions nor `FiniteTypeTarget`, `MainTarget`, the whole manuscript, a PR, or a phase. The new propositions are specifications, and all their geometric construction obligations remain to be proved.

The review read AGENTS.md, the objective, unchanged manuscript cor:liouville and its proof, the new statement/crosswalk, actual unchanged Statement.lean and Geometry.lean, and the pinned interfaces identified below. It performed source inspection and inspected managed compilation receipts; it ran no Lean build, changed no semantic source, and made no network request. The only reviewer-authored artifact is this report.

## Findings

1. **Source fidelity and quantifiers.** `ConstructionTarget` takes arbitrary natural dimension d, the original LiouvilleDomain D and Completion C, compatible A, and cylindrical J data. `Radius C A` is its existential output. Smoothness, properness, lower bound, agreement with exp(t) for exp(t)≥2, core bound and compactness, primitive identity and dual norm identity are obligations in that output. They are not inputs to the unconditional construction. There is no reference-change freedom, assumed global Moser flow, MainTarget premise, or comparison conclusion in this target.

2. **Exact manuscript radial data.** On R>2 the requested identities are β=−dR∘J and |dR|²_(g dual)=R, with the original β, J and g. These give precisely the manuscript reference constants c=1 and rstar=2. The strict far-end cutoff includes its boundary slice in the compact remainder; equality at exp(t)=2 is explicitly required. Properness is native `IsProperMap`, and smoothness uses native `ContMDiff`. No metric completeness or primitive growth bound has been introduced.

3. **Witness conversion is honestly conditional.** `GrowthWitnessTarget` takes any `Radius C A` as an intermediate input, then preserves the *same* admissible B and positive C₀ in the compact-exception conclusion. This conditional lemma alone cannot discharge construction. `ConsumerTarget` removes that input: it existentially outputs P before quantifying T, fixes P.exactStructure to completionReference C, uses HEq to fix its dependent compatible structure to A, and fixes c and rstar. Its premise matches the end-growth existential in unchanged FiniteTypeTarget. No monotonicity of B or restriction to a selected growth function is assumed. Weak taming is not needed for this geometric conversion; its omission does not change the unchanged corollary's weak-taming hypothesis.

4. **Native metric and norm meanings.** CompatibleStructure.g is a native smooth Riemannian metric with g(v,w)=dβ(v,Jw). `MetricTangent` has the norm obtained from this metric's `toCore`, and its proved `tangent_norm_eq` binds that norm to sqrt(dβ(v,Jv)). `covector_apply` verifies transfer of the same covector into that metric norm; `dualNorm` is its continuous-linear operator norm. `inverseNorm` uses the inverse positive contraction from the g-dual to g-tangent, constructed using nondegeneracy and finite dimension. Its equation is established in Geometry.lean. Neither inverse norm silently uses the default chart norm.

5. **Actual complete Liouville geometry and sign.** The pinned Completion contains a CompleteLiouvilleManifold with actual Flow ℝ, jointly smooth action, and a chart ODE at every real t. Flow has the real-addition and zero laws; this is not a forward semigroup or an arbitrary operation. Both LiouvilleStructure and CompleteLiouvilleManifold use dβ(Z,v)=β(v). Completion.end_flow identifies its end parametrization with that same flow, while end_primitive is exp(t)α. The cylindrical formula sends the time direction to Reeb and has second component −α(v), agreeing with J(r∂r)=Reeb at r=exp(t). The new T is correctly termed ExactSymplecticStructure and need not have a complete primitive. No inference of completeness from an exact gauge change is made.

6. **Pinned bridges really apply without extra hypotheses.** `endMap_injective` derives all-real-time injectivity from the original nonnegative end embedding and flow. `endMap_isLocalDiffeomorph` uses the actual native inverse-function machinery. CompletionCollar constructs the open escaping basin, inverse coordinates and their smoothness and the end diffeomorphism. CompletionCollarExtension proves boundary compactness from the compact carrier/frontier embedding and proves endMap membership in the compact image iff time≤0. These declarations quantify over the original arbitrary C. Dimension zero is handled by CompactDomain.zero_boundary in the pinned local-diffeomorphism proof; no positive-dimension or nonempty-boundary assumption is missing from the new targets.

7. **Crosswalk and intended construction.** The crosswalk distinguishes available proved end-coordinate/compactness interfaces from the remaining radial and metric obligations. Its cutoff profile has the stated endpoint values and bounds under the inspected native smoothTransition convention. The suggested smooth gluing, properness and metric identities still require Lean proofs. The old cluster GeometryTarget snapshot was inspected at the nested path listed below: its complete-flow/sign reuse claim is accurate. Its existing cutoff examples do not replace the present manifold construction. A negative reuse-search result is not a mathematical completeness claim about all library contents.

## Compilation evidence and limitations

`verification/finite-type-radial/statement-check.json` records a passed managed build of `ExactLiouvilleComparison.FiniteTypeRadialStatement`, returncode 0, ok=true and snapshot_verified=true, source key `2146d3344d78ffa4b63325047f7d7ae4e0f3b58ff46ef3323f9402305475a681`.

The first inventory diagnostic failed on the unsupported printer option `pp.maxDepth`, not on statement elaboration. The parent corrected the diagnostic and then used explicit file export to preserve elaborated declaration types, the namespace inventory and `Lean.collectAxioms` results. The final `verification/finite-type-radial/statement-inventory-check.json` records a passed managed check of the current StatementInventory.lean, returncode 0, ok=true and snapshot_verified=true, source key `7279a63d6d71f58bb5581c39d9b4f68a8878b21a4cbde4889914b8eef11e1b93`. The source key is recorded exactly in the receipt bound below; see that receipt for authoritative machine metadata.

The reviewer inspected the diagnostic source and saved names/axioms and sampled the elaborated structure/projection types against the semantic source. The inventory contains 29 namespace declarations, including generated constructors/projections; every recorded transitive axiom is among propext, Classical.choice and Quot.sound. The three target definitions elaborate to Prop, so their quantifier bodies were reviewed directly in source, not inferred from a type print of `: Prop`. This declaration audit does not audit future construction theorems. No independently executed build or full final proof audit is claimed. The target module contains definitions and an output structure, not a construction proof. Future proofs require their own checks, source bindings, axiom audits and proof review.

A direct diff against the baseline showed Statement.lean, Geometry.lean and the authoritative manuscript unchanged. Actual dependency HEADs were checked: FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; managed receipt toolchain is Lean 4.34.1. Semantic changes to the reviewed targets or crosswalk require renewed review.

## SHA-256 source bindings

Paths are relative to the objective workspace unless absolute. These bind the exact bytes inspected, including the successfully checked final diagnostic source and preserved exports.

| Source | SHA-256 |
| --- | --- |
| `AGENTS.md` | `779b846ce732d3f81e859d536d7f31e4354a1650ace887d37e68c3b36abf654a` |
| `docs/objective.md` | `0f7ca4a2449cca3d400e7afda913364582be71f858fe31475fa60665502ce5e8` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `docs/finite-type-radial-crosswalk.md` | `291daffcb519975c8db5c1b7875bbe72e7f4d05024e576a386a2a435424f42fc` |
| `ExactLiouvilleComparison/FiniteTypeRadialStatement.lean` | `5c628a902112976da8252a44f55801395c715526b11e3bfe362fbdbfbb200daa` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `verification/finite-type-radial/StatementInventory.lean` | `736ab5f6ac76f0afa735a93ae759114a4a568b436f8bf857d80d6c0424edf909` |
| `verification/finite-type-radial/statement-check.json` | `adf0c697a3a67c25558d2a6406c21dfa4ca16daf7f339667bdcd4e15abbc19c1` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Liouville.lean` | `d51b04337e39b31ab1b1d3b20093ba5956b8ea0b04456e141ef4c827268b335e` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| `.lake/packages/fsfltz/FsFltz/Geometry/FixedAmbient.lean` | `8fcedb064de005c2d236a425cebcbd0dfc137c8f102070592cb5eef9efb60d16` |
| `.lake/packages/fsfltz/FsFltz/Geometry/BoundaryMapBridge.lean` | `cf61339ff0650efec23fcd9a231bf51562ec066979ed866134958ed75de9bd44` |
| `.lake/packages/fsfltz/FsFltz/Geometry/BoundarySmooth.lean` | `f7e0bf01311b03f66f3a811cb6685708ca4fd1a4d131ea790fca3ce14c6e3b56` |
| `.lake/packages/fsfltz/FsFltz/Geometry/CompletionCollar.lean` | `658f83a5c5bdf00b64537fae385bcc77a9f22cb1d8760eb131e177aa92a372cb` |
| `.lake/packages/fsfltz/FsFltz/Geometry/CompletionCollarExtension.lean` | `14223c36cbd0741d29d682fd5fe4a64903819a551e6056451c1b2be47b5f1f6d` |
| `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` | `044b397c80cc85430415afd4f976195943dd0015170cd0388d445dc09098c979` |
| `.lake/packages/mathlib/Mathlib/Topology/VectorBundle/Riemannian.lean` | `0843d63047ded5737ec11933b101f258748f6efa8a31c4934893d044ff44b2e5` |
| `.lake/packages/mathlib/Mathlib/Dynamics/Flow.lean` | `699d26276fb429c6159bb0c1d518bcd0a1a01d1cfb769f46a4a5131b2c002cfb` |
| `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean` | `0feea244614398679aac0efdf3c67e72c1d246f103d48ae1dbb8d40d0e75ccfa` |
| `/var/lib/archon-worker/imports/project-reference/archon_liouville/cluster-source-2c239b0/Hu-Mingyuan-cluster-skeleton-2c239b0c03922a1549f18ee3a45a8e0ca25bb28c/ClusterSkeleton/GeometryTarget.lean` | `20b2a5214e6f3abb0e2ab936c479fd386c27c160d69dee94f1d6215e79f006ac` |
| `verification/finite-type-radial/statement-inventory-check.json` | `fcd9579b02d15b16cb0e7d023a1b486164604b46d2124d43757126be67fb98bc` |
| `verification/finite-type-radial/statement-inventory.names` | `f23bdd72619a733c9efdd12c9081e301e0d75281e088003ae60359c3df27b93c` |
| `verification/finite-type-radial/statement-inventory.types` | `792a79274a4fa381925ee1f60347286ad1a6aae764b6d93c4e292209a37f4fc6` |
| `verification/finite-type-radial/statement-inventory.axioms` | `b4d57c9ddab60f03d356e77df365cd4bca9bcec88d9d58abcbcf8bd5d6260680` |
