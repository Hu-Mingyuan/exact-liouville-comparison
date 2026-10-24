# Independent final review: native finite-type presentation

Mission `2cde2f71-9a68-4bf2-86cd-cfc13d8268cb`. Reviewer: independent `presentation_review` agent. Verdict: **accepted for the bounded native source-domain adapter on its actually constructed quotient**. No blocking findings remain in this adapter. This is not combined root-objective acceptance, a cylindrical-J existence theorem, arbitrary-completion transport, or GitHub publication acceptance.

## Reviewed version

The reviewed private proof commit is `7fafdc3c53d58d2b4357c6e798d30b2469455781`, publication `3fba0167-a3d8-43e8-892e-4a96388fbd1d`, repository `31e09b7d-6080-4383-8e4e-92b14780690a`, branch `horizon/changes/0c107de4-e292-4d2b-9749-39cadc372f34`. The reviewer read its publication receipt, which verifies the exact requested tree delta against parent `d3523f6f68fa8e68424190bdb982331a800467dd`. The parent is the independently accepted compiled statement stage. Publication verification is distinct from the Lean evidence below.

| Reviewed source | Independently checked SHA-256 |
| --- | --- |
| `FiniteTypePresentationStatement.lean` | `1c0a143611518562a99d2de11002165cc19905ca25e10cb873aaf7b7691cbc0d` |
| `FiniteTypePresentation.lean` | `a9269d25d698f9265bedebb8bb97c9605b486cd169f766302424682252c8ad01` |
| `FiniteTypePresentationConsumers.lean` | `2b6f4931ba44b7e15e1c5c0abee8d6b2b4bf9da244e2e7e60190255ebf44b9f7` |
| `docs/finite-type-presentation-crosswalk.md` | `bb974415f900333d6f185342b3febfb638cef1aabfa427b43519be36988cc092` |
| `docs/finite-type-presentation-proof.md` | `510f0fb571109bbc3c140a9080a736676beec4c643193645b06d0193958b0740` |
| `scripts/verify-finite-type-presentation.py` | `035a9b974e0a62cae8ffad6a6acd42f7d6e0cb8cde81cf3173909726c638736f` |
| `verification/finite-type-presentation/Audit.lean` | `32cb818ee823a4924670012ff2d8e4bce9f0534bc82830a728bb80284c804f43` |

The first three filenames above are under `ExactLiouvilleComparison/`. The statement and crosswalk match the pre-proof gate exactly.

## Proof and definition assessment

The reviewer read the complete new statement, implementation, consumers, proof guide, audit driver and reproduction script, with the native upstream constructors and bridges inspected during statement review. The actual elaborated types of `nativeTarget`, `exists_quotientData`, `comparisonFromNative`, and `Consumers.nativeComparison`, and the elaborated definitions of `NativeTarget` and `fromNative`, were inspected to check source assumptions and quantifier order.

`exists_quotientData` extracts the native collar and quotient Liouville structure directly from `IntrinsicLiouville.exists_liouvilleStructure_from_native`. Every stored preservation law is an output of that proved constructor. `fromNative` chooses this proved witness from the native source data alone. It neither accepts nor depends on a comparison, cylindrical structure, arbitrary completed ambient, or Moser flow.

`QuotientData.identifications` proves the reviewed conjunction. The actual original map is smooth and a closed embedding, its native differential is bijective even at boundary points, and its range/frontier are the exact compact carrier/native boundary image. The completion inclusion is definitionally identity. Full primitive preservation uses `native_primitive`; native field preservation composes `canonical_field` and `native_field` with the correct orientation. The original boundary inclusion and restricted boundary form are the actual pinned ones. The end equality uses the actual complete boundary orbit and `boundaryOrbitMap_eq_outwardEndMap` on `-width<t`; the all-real exponential law uses `completion_original_end_primitive`. These are geometric bridge theorems, not arbitrary replacement operations.

`QuotientData.comparisonFor` passes this very domain, completion, selected `A`, cylindrical witness, target primitive, weak-taming proof and original growth proof directly to `FiniteTypeComparison.finiteTypeTarget`. The existing witness-unpacking theorem supplies the native conclusion. `nativeTarget` constructs the existential witness and both required clauses; it is an actual theorem of the pre-reviewed `NativeTarget`, not a replacement target proposition. `comparisonFromNative` exposes the selected quotient to consumers.

No hypothesis is silently strengthened or conclusion weakened. The native source remains a compact Hausdorff second-countable smooth half-space manifold of dimension `k+1`, with an actual native one-form, local open smooth coefficient extensions, nondegenerate actual exterior derivative and the pinned local outwardness condition. The native field is primitive-determined with `dα(Z,v)=α(v)`. Local outwardness requires nonpositive defining-function germs, nonzero differential and positive field derivative, not a global defining function or a preconstructed collar.

The completed ambient carries the actual jointly smooth complete Liouville flow for all real times and the actual chart ODE. The boundary end is only required to embed for nonnegative time; its orbit and primitive law hold for every real time. The original compact primitive is preserved on full tangent fibers, rather than just the contact distribution. Logarithmic time satisfies `r=exp(t)` and gives the literal original exponential boundary primitive.

The quotient is fixed before choosing `A` and the target exact primitive. The consumer retains exactly the selected `J`, the explicit metric `g=dλ₀(.,J.)`, its dual norm, and the inverse-contraction operator norm. The target remains merely exact symplectic, weak taming remains nonstrict, and the growth premise keeps arbitrary admissible `B`, a positive constant, a nonnegative eventual cutoff and the uniform bound at every end point using `B(exp(t))`. No metric completeness, target-primitive completeness, primitive-growth condition, supplied exhaustion or assumed Moser evolution is added.

The consumer tests meaningfully expose full original primitive and field preservation, positive contraction, literal attached end, all-real exponential law, all-real chart ODE, retained metric/dual/operator norms, and the actual diffeomorphism/gauge/isotopy conclusion. The source-geometry consumer retains the remaining embedding/carrier/frontier/boundary clauses. The proof guide accurately describes this implementation and its scope.

## Verification evidence independently checked

The reviewer did not rerun builds or modify proof sources. The full `final/receipt.json` was parsed and its recorded evidence checked against local files:

- All **3,902 source SHA-256 bindings** match the current files, including the **3,853 imported non-core source bindings**, the unchanged manuscript and accepted comparison source. Core modules are separately bound by the toolchain.
- The consumer-module build, Lean audit and direct consumer check all report `passed`, return code `0`, `snapshot_verified: true`, Lean `4.34.1`, and the common source key `2b675e79355f5670dde8072ee1cddf0d156fd6072535d301c4f534ea6ed082f7`.
- The audit covers **26 source declarations** and **123 elaborated declarations**, including the actual native target, direct consumer, upstream completion constructor levels, complete-flow definitions, and existing comparison interface. Every one of the **123 type artifacts** and **53 definition artifacts** matches its stored and uncompressed hashes and lengths.
- The independently computed union of all 123 transitive axiom sets is exactly **`Classical.choice`, `Quot.sound`, `propext`**. No additional axiom occurs. The checked source contains no admitted proof or replacement axiom.
- The reproduction script checks frozen statement bytes, preserved accepted source bindings, dependency pins and clean source trees, disallowed declarations/axioms, declaration coverage, exact import-source resolution and source drift. Its Lean audit uses `Lean.collectAxioms` transitively. These checks substantiate this bounded claim; the proof bodies and actual interface meanings were independently reviewed rather than inferred from successful execution alone.
- The split archive's two part hashes, concatenated hash/length, and all **185 archive member hashes** match `audit-archive.json` and the local evidence. `final/receipt.json.gz` hashes correctly and decompresses byte-for-byte to the inspected full receipt; its uncompressed SHA-256 is `9cd0bbb89ebe2bb902f363323474b0f05db452ece06df5bb2d5c816c5f6c5de6`. This packaging preserves the evidence despite the per-file publication cap.

## Acceptance boundary

This closes the promised native-source adapter for the constructed quotient with the chosen cylindrical compatible structure retained. It makes no theorem identifying an arbitrary independently supplied completion `X`, no zero-dimensional native-domain construction beyond the upstream `k+1` scope, and no construction or extension of a cylindrical compatible `J`. Those are explicit scope boundaries, not hidden input assumptions. Combined integration, any separately owned cylindrical-J work, final project packaging and any eventual GitHub upload remain outside this review.
