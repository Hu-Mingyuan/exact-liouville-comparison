# Independent final source-bound review

**Verdict: PASS for the bounded cylindrical end derivative and exact metric
calculation. No repairs required.**

Reviewer: independent `metric_review` agent, mission
`0b5b2f0c-3dfa-4741-ac55-30976cabd107`, 2026-10-24. This is the same independent
reviewer who accepted the pre-proof specification, not the proof author.

## Exact reviewed implementation

This verdict binds private implementation commit
`1b130f41e1652239cc6a08074d525e7b60f6319e`, repository
`31e09b7d-6080-4383-8e4e-92b14780690a`, branch
`horizon/changes/49cb3f33-f880-4108-94ba-0039a6903ecd`, based on
`f8b5b6bcb56a18c0094d15fed4619ff100327e30`.

I inspected the local publication receipt and upload bindings, then independently
checked all 22 file hashes against the local reviewed bytes. Every binding's
artifact ID matches the corresponding requested operation, and the bound path
set equals the receipt's verified changed-path set. Publication
`16640d21-5e1a-448a-ab84-176a06db8b81` records `git_tree_delta` verification of
the exact file operations, commit parent, and preservation of other entries.
The operation ID is `49cb3f33-f880-4108-94ba-0039a6903ecd`; its idempotency key
is `bee7ebb9-54b1-454c-a2e9-d8b43dc07ed1`. This publication receipt explicitly
does not include Lean validation; the separate managed receipts below provide
that evidence. This is a private project commit, not a GitHub publication.

The review file itself is to be added as a review-only descendant. It does not
change any reviewed Lean, statement, or semantic bytes. Future changes to those
bytes require renewed source binding and appropriate checks.

## Statement fidelity and noncircular inputs

The statement module, crosswalk, and pre-proof review retain exactly their
accepted hashes. The authoritative manuscript and the existing `Statement`,
`Geometry`, and `LinearAlgebra` modules retain their receipt-bound hashes.
The earlier statement review remains applicable without qualification.

The accepted theorem is
`ExactLiouvilleComparison.FiniteTypeRadialMetric.target : Target`.
The full declaration inventory confirms that this theorem and
`checked_target` have exactly that type, with no extra section variables or
hidden premises. `Target` still quantifies every natural dimension `d`, an
actual `LiouvilleDomain d`, its unchanged `Completion`, the original compatible
structure `A`, its cylindrical structure, and any native smooth real function
`R` satisfying only the literal `EndRadius` value equality. Its conclusion
holds for every end point with `t > log 2` and every ambient tangent vector.

No derivative identity, metric estimate, norm bridge, gradient identification,
Moser flow, comparison map, or target conclusion is supplied as an additional
input. There is no positive-dimensional restriction. The zero-dimensional
case is handled by the empty boundary in the proved upstream local
diffeomorphism theorem, preserving the arbitrary-dimensional interface.
The underlying manifold, tangent spaces, derivatives, exterior derivative,
primitive, and compatible structure remain the actual native geometric data.

## Proof checked

I read the complete implementation and both nontrivial consumers, and inspected
the actual pinned `BoundarySmooth` and `FlowBridge` definitions/proofs used by
the new proof, together with the original metric inner-product instance.

1. `end_derivative_surjective` extracts the surjectivity of the native
   derivative from the continuous linear equivalence provided by
   `Completion.endMap_isLocalDiffeomorph`. That upstream theorem proves the
   local diffeomorphism from the actual immersion and finite-dimensional rank;
   it is not an assumption introduced for this result.
2. `radius_end_derivative` first obtains a genuine neighborhood on which
   `exp(p.2) > 2`, using continuity and the strict tail hypothesis. It applies
   the literal end equality there, uses equality of native derivatives of
   germs, and applies the native manifold chain and projection derivative
   rules. The result is exactly
   `dR(d endMap(v,s)) = exp(t) * s`. It does not differentiate an isolated
   pointwise equality or silently use a boundary derivative.
3. `end_time_derivative` differentiates the smooth map `s ↦ (y,s)` and then
   `endMap`. The curve is identified by `Completion.end_flow` with the original
   complete flow orbit. Pinned `CompleteLiouvilleFlow.isMIntegralCurve` derives
   the native manifold ODE from the jointly smooth action and actual chart ODE
   for all real times. Evaluating its derivative on `1` proves
   `d endMap(0,1) = C.ambient.field`. The field or flow is never replaced.
4. `primitive_identity` uses surjectivity to cover all ambient tangent vectors,
   derives `t >= 0` from `t > log 2`, applies the cylindrical J equation, the
   newly proved radius derivative, and `Completion.end_primitive`. The signs
   give exactly `beta(v) = -dR(Jv)`.
5. `field_inner` uses the original `A.metric_inner_eq`, positive contraction
   `d beta(Z,v) = beta(v)`, the primitive identity applied to `Jw`, and
   `A.square`. Thus `g(Z,w) = beta(Jw) = dR(w)` with the required convention.
6. `radius_dualNorm_sq` identifies the actual transferred native differential
   `A.covector ... (mfderiv ... R ...)` with the Mathlib Riesz image of the
   actual Liouville field. The isometric Riesz map and the inner-self identity
   give `dualNorm(dR)^2 = g(Z,Z)`. The proved gradient and time-tangent
   identities then give `g(Z,Z) = dR(Z) = exp(t) = R`. Every equality is proved;
   no norm assertion is an input.
7. `target` combines the two required conclusions. `end_consumer` converts
   the strict condition to `2 < exp(t)` and exposes equality to `exp(t)`.
   `radial_fields_consumer` uses the parent's literal `c = 1` convention and
   obtains the radial bound from the stronger proved equality. It constructs
   no global radius and claims no `RadialReference` or comparison theorem.

The metric check is substantive: the unchanged
`LinearAlgebra.metricInnerProductSpace` is `InnerProductSpace.ofCore` of the
same core that defines `A.MetricTangent`'s norm, and `metric_inner_eq` is
literally `A.metric_eq`. Thus the Riesz argument uses the original
`A.g = d beta(.,J.)`; it does not switch to the chart norm. The native
`mfderiv` is transferred by the value-preserving `A.covector`, as in the
reviewed definition crosswalk.

The Liouville completeness claim also remains literal. The original
`CompleteLiouvilleFlow` contains `Flow ℝ`, joint smoothness and the chart ODE
for every real time. The new proof reuses this flow and a proved ODE bridge.
Nothing weakens it to forward completeness or an assumed Moser evolution.

## Managed checks, inventory, and transitive axiom audit

I checked the verification script, the inventory and axiom source programs,
the raw managed logs, and the receipt. All three serial checks passed with
return code 0 and `snapshot_verified: true` at the same source key:

`43002979bb64d34c1c315f243b036f0ef6c69ff49500341a9075da12fdb4b019`.

The checks are the `FiniteTypeRadialMetricChecks` build, the declaration
inventory Lean program, and the axiom Lean program. Their log records exactly
match those in `receipt.json`. The first check reports up-to-date targets;
it is not represented here as a fresh uncached rebuild. The native toolchain
is Lean 4.34.1, with the stated pinned FsFltz and Mathlib revisions.

I independently verified every `source_sha256` and `dependency_sha256` entry,
every inventory part hash, and the concatenated inventory hash. The three
numbered inventory parts concatenate byte-for-byte to 1,467,682 bytes and
decode as full UTF-8. There is no omitted `⋯` placeholder. The complete
inventory's top-level declaration names exactly match `inventory.names`.
All 12 source declarations appear among the 13 environment declarations;
the additional declaration is the generated `EndRadius._proof_1`.

`Axioms.lean` uses `Lean.collectAxioms` for every declaration in the owned
namespace, including generated/private-prefix names. The raw audit exactly
matches the receipt and the inventory name set. Every transitive axiom set
is a subset of `{propext, Classical.choice, Quot.sound}`. In particular, the
actual proved `target`, its consumer, and all intermediate theorems have
allowed-only transitive dependencies. No `sorryAx`, custom axiom, admitted
proof, or circular imported theorem occurs in this audited result.

No additional build was necessary: the exact bytes and passed managed receipts
resolve the review questions. This review performed read-only checks and
wrote only this file.

## Hash binding

The complete source and dependency manifest is in the bound `receipt.json`.
Key SHA-256 values are recorded here to make the verdict unambiguous:

| Artifact | SHA-256 |
|---|---|
| `FiniteTypeRadialMetric.lean` | `de6919a3c85f40318c71007472b3dcb63749df9d1f8f9afaefc549249a50424d` |
| `FiniteTypeRadialMetricChecks.lean` | `5223aff14359cd5d20c05b4551cccc8ef7231aa4d436dfd297fadc38fd86fd06` |
| `FiniteTypeRadialMetricStatement.lean` | `19e07aded10817181abdf3b74effff7c29a2f3dd1dda6e2c45e8dbfb1356cbad` |
| `docs/finite-type-radial-metric-crosswalk.md` | `b5ac34f09ac0f4113de20a10838d4eca69ee11554b32180e785c11fb94c47d72` |
| `docs/finite-type-radial-metric-proof.md` | `62175b424fe44ab043ec0191563531527d355a199b3ec06e3cbcfe5992aff9f8` |
| `verification/finite-type-radial-metric/statement-review.md` | `079d47fb1c0b53c77e0da1c92ec381eb9d9979dda0d64ff6f6b8c80948adafdc` |
| `verification/finite-type-radial-metric/receipt.json` | `1ec30d6edfa416b1bb542010331de78bae013b974bc40782216f154cac4dc0bd` |
| Full concatenated inventory | `1cfd61daec87b9cad3a0b7361c1f7ec84cb8fa6832915557874004e7731692ea` |
| `$TMPDIR/finite-metric-publication.json` | `7f86104040bd9710a6d96c1d831b99f463df9d95500aaad401f25216d8627657` |
| `$TMPDIR/finite-metric-upload-bindings.json` | `be131befe27d1f7651872705bc6fd900b2b28881032d308a8b10795acc30a79c` |

## Acceptance boundary

The bounded mission is accepted: actual proofs establish the native end
derivative, original Liouville time tangent, primitive identity, exact original
g-dual norm square, and the advertised consumers, with source-bound checks and
allowed-only transitive axiom audit. This completes the local calculation in
the proof of manuscript `cor:liouville`, lines 402–409, for a supplied smooth
radius satisfying the accepted end equality.

It does not prove existence or properness of that radius, global radial-reference
construction, growth conversion, `FiniteTypeTarget`, `MainTarget`, or the other
comparison corollaries. The proof guide states this boundary accurately.
The parent retains those constructions and integration. No claim of full
objective completion, final standalone acceptance, final PDFs, or GitHub upload
is made by this verdict.
