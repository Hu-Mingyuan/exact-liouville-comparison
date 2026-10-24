# Finite-type radial reference: bounded delivery

Mission 9329795b-7d27-46a3-adb3-79b3711aaf56. The actual bounded construction is
proved; this delivery does not prove FiniteTypeTarget or MainTarget.

## Integration interface

Import `ExactLiouvilleComparison.FiniteTypeRadial` (or
`ExactLiouvilleComparison.FiniteTypeRadialConsumers` for the explicit checks).
For the unchanged `C : Completion D`, original compatible `A`, and
`cyl : CylindricalStructure C A`, use:

* `FiniteTypeRadial.reference C A cyl : RadialReference C.ambient.manifold`.
* `FiniteTypeRadial.reference_growth C A cyl T h` to convert exactly the
  existential end-growth premise of FiniteTypeTarget to GrowthAtInfinity at
  that constructed reference, with A literally unchanged.
* `FiniteTypeRadial.constructed_growth_witness` (from the Consumers module)
  to retain the particular original admissible B and constant C₀ with a proved compact exception.
* `FiniteTypeRadial.radius_primitive` and `radius_dual_sq` for the literal
  primitive identity and exact g-dual square outside R≤2.

The reference preserves completionReference C and A definitionally. Consumer
lemmas additionally expose equality of the original primitive, J and g, and
c=1 and rstar=2. The radius is smooth, proper, at least 1, equals exp(t) when
exp(t)≥2, and is at most 2 on the compact complement of the strict end above
log(2). Its construction does not assume a radius, metric identity, Moser flow,
comparison, metric completeness, or additional dimension restriction.
Theorem `constructionTarget` proves the reviewed construction specification;
`consumerTarget` proves the reviewed unconditional output interface.

## Source and verification

Implementation commit: `9acd2ca5be07c490e1d9d48ac3e938390ac9a987`, private
repository `31e09b7d-6080-4383-8e4e-92b14780690a`, branch
`horizon/changes/55d29ac6-904d-4934-979d-3aab109eefb3`.
Verified publication `b39f54d0-502c-4cae-96fc-9a94fe0055c4` establishes the exact
25-file delta over unchanged metric-child delivery
`9716da2fdab7d268cfea6fbc3808a40cf3a47546`. The final review and this handoff are
added in a documentation-only descendant, whose exact commit/publication are
recorded in the mission ledger.

Reproduce with `python scripts/verify-finite-type-radial.py`. The script checks
preserved baseline and child-source hashes, actual dependency pins, then runs
the consumer build and full transitive audit serially through the managed
checker. Both accepted checks have `ok=true`, `snapshot_verified=true` and
source key `67617b8b6dadf88867ea5dde583c25bbaa52d86cf690b36503b64991e06586c8`.
The preliminary out-of-date detection in the build log is followed by actual
successful assembly/consumer compilation, not an unresolved build error.
An earlier resource-exhausted invocation is superseded by these passed checks.

`verification/finite-type-radial/receipt.json` contains source/dependency hashes
and all check receipts. The inventory covers 59 source and 95 elaborated
(including generated/private) declarations in the two owned namespaces. The
full explicit inventory, including proof arguments and deep terms, is
losslessly compressed as `elaborated-types-full.txt.gz`; its decompressed hash
and byte count are in the receipt and it contains no elision. The accompanying
`elaborated-types.txt` is readable. Only propext, Classical.choice and Quot.sound
occur in the transitive audit. The earlier statement inventory is preserved
losslessly as `statement-inventory.types.gz` to reconstruct the exact bytes
bound by the pre-proof review.

Independent pre-proof review: `verification/finite-type-radial/statement-review.md`.
Independent final source-bound review: `verification/finite-type-radial/final-review.md`.
The inherited metric child has its own statement/final reviews, source hashes,
managed checks and full inventory in `verification/finite-type-radial-metric/`.
The combined audit also covers its imported declarations and dependency closure.

## Ownership and limits

No mission criterion was removed or corrected. All original semantic modules,
authoritative manuscript, old project and pinned upstream sources are preserved.
No GitHub upload or final PDF was made.

Root mission 91f6a7c7-1eb9-4e2c-bb7e-39389d62ea18 retains application of
MainTarget to obtain FiniteTypeTarget, other corollaries, source coverage,
whole-project integration/acceptance and final packaging. MainTarget owner
92dedb29-ffc9-40f9-8d8c-07db9fc6ffbe / assignment
351c91eb-6593-42c6-8345-afc5de6e5374 is unchanged. This delivery assumes no
result from that owner and claims no comparison theorem.
