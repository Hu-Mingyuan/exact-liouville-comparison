# Stein and common-reference comparison proofs

Import `ExactLiouvilleComparison.SteinComparison` or
`ExactLiouvilleComparison.CommonReferenceComparison`. The actual proof terms are
`SteinComparison.packagedSteinTarget`, `SteinComparison.steinTarget` and
`CommonReferenceComparison.commonReferenceTarget`. Their types are the unchanged
`PackagedSteinTarget`, `SteinTarget` and `CommonReferenceTarget` in `Statement.lean`.
This delivery is bounded to these applications. Finite-type application and full
`ManuscriptTarget` acceptance remain with the existing finite-type and root
owners; no final PDFs, root-import changes or GitHub upload are included.

## Stein application

`SteinComparison.growth` supplies `SteinRadial.radius_proper` and `radius_lower`
to `SteinGrowth.steinRadius_growth`. The delivered extension is smooth within
[1,∞), positive, dominates r, and retains divergent integral and equality with
the original B above e+2. Its compact exception is K union {R≤e+2}. The same C,
metric, symplectic form and inverse contraction norm are used.

`SteinRadial.reference i P` retains the exact P.exactStructure and P.compatible.
It supplies R=exp(1)+‖i.map‖², c=1/4 and rstar=2 with all radial hypotheses
proved by the delivered construction. The local `radial_inner_eq`,
`radial_dualNorm_eq`, `radial_inverseNorm_eq` and `radial_weaklyTames_iff` are
explicit definitional bridges. No norm on a chart replaces the induced metric.
The delivered `metric_norm_eq` identifies the tangent g norm with ‖di(v)‖,
and its dual estimate is ‖dR‖g*²≤4(R−e).

`packagedSteinTarget` applies the actual `MainComparison.mainTarget` after this
growth conversion. It works for every packaged SteinReference, not only one
construction. `steinTarget` outputs `SteinReferenceConstruction.reference i`
from the original proper complex embedding and then proves the comparison for
every T. The output reference has β=−(1/4)dR∘J and the literal induced Euclidean
metric; no extra reference, finite-type geometry, metric completeness or
primitive completeness is an input.

`comparisonWitness` exposes the actual `MainComparison.comparisonMap` and
`comparisonGauge`, at `SteinGrowth.extend B` and the explicit enlarged compact
exception. These are the delivered four-path Moser endpoint Ψ⁻¹ and −f∘Ψ⁻¹.
All applicability premises are discharged. `CorollaryComparisonConsumers` gives
`referenceIdentities` and `steinNativeConclusion`: actual diffeomorphism F,
smooth h, a smooth identity-start isotopy with jointly smooth inverse, the
literal primitive identity and the exterior-derivative identity. Its source
hypotheses mention only the embedding and T with weak taming and growth.

## Common-reference application

`commonReferenceTarget` applies the delivered main theorem separately to T₁
and T₂ and combines the conclusions with `ExactComparison.commonReference`.
`explicitCommonTarget` keeps both native endpoint/gauge witnesses and uses
`ExactComparisonAlgebra.Witness.commonReference`. The map is exactly
F₂.symm.trans F₁ = F₁∘F₂⁻¹, and the gauge is (h₁−h₂)∘F₂⁻¹.
`commonNativeConclusion` unfolds both smooth isotopy families and the literal
primitive/exterior identities. `separateGrowthWitnesses` explicitly accepts
independent B₁,B₂,C₁,C₂,K₁,K₂. No growth bound on either primitive is added.

## Source-bound verification

Run `python scripts/verify-corollaries.py` from this checkout in the supplied
managed Lean environment. It checks every baseline file, the 108 exact private
input bindings, reviewed semantic hashes and pinned dependency revisions; then
runs three serial managed checks: library, complete elaborated inventory/axiom
audit, and native consumers. It checks nonelision, full new-module declaration
coverage (including generated environment names), every direct imported public
interface used in the application, allowed-only transitive axioms, and stable
source snapshots. The allowance is exactly propext, Classical.choice, Quot.sound.

`verification/corollaries/statement-review.md` records independent pre-proof
acceptance. `statement-hashes.json` freezes the original statement, geometry,
manuscript and bounded crosswalk/specification. `import-manifest.json` records
exact commit, blob and SHA-256 for source-selective inputs; the reproducible
import script rejects any mismatch in an existing file. All 307 source/evidence
hashes from the main delivery were also checked unchanged before proof work.
`final/receipt.json`, logs, per-declaration full types and axiom inventory bind
the checked implementation. The private publication and independent final
review are delivered as subsequent evidence with the exact commit identity;
they are not falsely represented as part of the earlier source snapshot.

This is an exact-symplectic comparison. An object called Liouville continues to
carry its actual positive-contraction, all-real-time complete smooth flow; no
such completeness is inferred from the existence of an exact gauge comparison.

Full type texts larger than 512 KiB use deterministic gzip compression to fit
the private delivery API. The receipt records both original text hashes and
stored-file hashes/paths; `gzip -dc FILE.txt.gz` recovers the complete nonelided
text. Compression removes no elaborated information.
