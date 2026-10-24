# Bounded manuscript assembly handoff

The unchanged FiniteTypeTarget and ManuscriptTarget now have actual proof terms.
Import `ExactLiouvilleComparison.ManuscriptComparison`, or
`ExactLiouvilleComparison.ManuscriptComparisonConsumers` for native output checks.

- `ExactLiouvilleComparison.FiniteTypeComparison.finiteTypeTarget`
- `ExactLiouvilleComparison.ManuscriptComparison.manuscriptTarget`
- `ExactLiouvilleComparison.ManuscriptComparison.completeLiouvilleComparisonTarget`

The finite-type theorem applies MainComparison.mainTarget to the unconditional
FiniteTypeRadial.reference and reference_growth. The original completion,
primitive, A, J, g, dual/operator norms, weak taming, and existential eventual
end-growth hypotheses are preserved. c=1 and rstar=2 are literal. No radius,
flow, norm estimate, completeness or comparison input is added.

The manuscript assembly uses the actual source-level SteinTarget proof, which
constructs its reference from the embedding, and the actual common-reference
proof. Consumers expose the native diffeomorphism, smooth gauge, smooth identity
isotopy and inverse family, with primitive and exterior identities. The complete
specialization retains the two prescribed CompletePrimitive flows for all real
times and positive contraction; MainTarget remains general exact symplectic.

## Exact private source and evidence

Proof/evidence commit: `63bef621295ce179f1836ff77d66532d1e2d4ebb`.
Repository: `31e09b7d-6080-4383-8e4e-92b14780690a`.
Branch: `horizon/changes/5a39f607-7960-485b-8f75-906dc2a19656`.
Verified publication: `f35222c3-fc85-46db-83d2-7286112ad4b1`.
Its source parent `81d06c2f0b84041f7733da2de754155782a7cf5f` integrates the
finite radial delivery into the unchanged Stein/common tree
`41e7528a6d0de96a657a7f570e0537bd5343a0fc`, which includes main delivery
`55493c9ba47cc09071f6abf0b16b901a95f19b1f`. All finite radial source is preserved
from `ebedffcffe9b1098ee28359e5fd00adc9cd05ad8`.

Run `python scripts/verify-manuscript-comparison.py`. Three serial managed
checks pass with snapshot_verified=true and common source key
`4840c779fdd4be2ee441da0ea97e682adec6eb82d4d9eadf647d5c4d1deab854`.
The receipt binds 383 source/dependency paths; the audit contains 26 new source
and 119 elaborated declarations. Full nonelided types and relevant definition
bodies, structure-constructor assumption fields, native consumers and transitive
axiom results are in `verification/manuscript-comparison/final/`. Only propext,
Classical.choice and Quot.sound occur. Validation reuses the managed caches;
it is not represented as an uncached dependency rebuild.

The independent pre-proof statement review and original crosswalk are retained.
The independent final review is stored as
`verification/manuscript-comparison/final-review.md` in a documentation-only
descendant. Private publication receipts and the final delivery manifest identify
that descendant separately; this handoff does not attribute later review files
to the earlier checked commit. Inherited reviews are bound to preserved source
in prerequisite-bindings.json. Statement.lean, Geometry.lean, manuscript,
dependency pins, upstream libraries and the old cluster project are unchanged.

## Acceptance boundary and retained owner

See `manuscript-comparison-crosswalk.md` for all four source statements and
`manuscript-comparison-proof.md` for the proof-to-code map. The explicit FsFltz
Completion and native real Cauchy–Riemann embedding presentations are retained.
Intrinsic completion-presentation equivalence, conversion from Mathlib complex
holomorphic embeddings and existence of a cylindrical J are not newly proved.
These are reported source-presentation limits for broader acceptance, not hidden
assumptions introduced into the unchanged formal targets.

Root mission `91f6a7c7-1eb9-4e2c-bb7e-39389d62ea18` retains global acceptance,
final exposition/LaTeX/PDFs, CI/release packaging and final operator GitHub delivery.
This mission supplies bounded application/assembly and exact private evidence;
it performs no phase acceptance, final PDF creation or GitHub upload. No target
correction or criterion removal was made.
