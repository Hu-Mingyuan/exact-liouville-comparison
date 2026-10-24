# Independent final review: Stein and common-reference comparison

**Verdict: ACCEPT the bounded corollary proof delivery. No blocking findings.**

Mission `b518dc8e-9cf8-40a0-b7dd-1199bf9c17a3`, revision 1. Independent reviewer
`/root/final_review`, 2026-10-24, applying
`$HORIZON_SKILLS_DIR/subagents/reviewers/mathematical-fidelity.md`.
This is a source-bound mathematical and Lean integration review, not a formal PR
review. I made no implementation, statement, dependency, or receipt edits.

Accepted actual exports are `SteinComparison.packagedSteinTarget`,
`SteinComparison.steinTarget`, and
`CommonReferenceComparison.commonReferenceTarget`, with constructed and explicit
witness variants, metric/growth bridges, and the native consumers. Their types
are the unchanged `PackagedSteinTarget`, `SteinTarget`, and
`CommonReferenceTarget`; these are proved theorems, not merely propositions
naming future obligations. This verdict excludes the finite-type corollary,
full `ManuscriptTarget` acceptance, final PDFs/release packaging, and GitHub
publication. Existing finite-type and root ownership remains unchanged.

## Exact publication and source identity

Reviewed private commit: `41e7528a6d0de96a657a7f570e0537bd5343a0fc`, repository
`31e09b7d-6080-4383-8e4e-92b14780690a`, branch
`horizon/changes/dc021676-d0d0-4eaf-8052-1d92b131e13a`.
I independently retrieved the operation using request key
`4faa6df3-f388-4a04-a922-b7d021e689b9`. It records publication
`ae5b521f-26d4-47f9-a4e4-50d7ff89bc89`, receipt artifact
`42adca2f-ea9c-4d85-b8b6-1f4ebd22aa54`, and a verified git-tree delta of 98
additions on parent `55493c9ba47cc09071f6abf0b16b901a95f19b1f`, preserving
unchanged entries. The publication receipt explicitly does not include Lean
validation; the separate Lean evidence below supplies that validation.

I independently fetched the 28 files in the final table through the authenticated
exact-commit repository file API. For each I checked returned commit/path,
complete decoded bytes, Git blob SHA-1, and SHA-256 against the local reviewed
file. All matched. No local Git object or local HEAD was assumed to represent
the private publication. The committed receipt binds 326 source files; I
recomputed every hash without mismatch. I separately verified all 108 prerequisite
commit/path/blob/SHA bindings against local bytes (102 distinct paths), all five
frozen semantic hashes, and all 267 files against immutable local baseline
`f8b5b6bcb56a18c0094d15fed4619ff100327e30`.

The unchanged independent pre-proof `statement-review.md` accepts the statement
and crosswalk before proof integration. I read that gate and confirmed its
frozen statement, original Geometry/Statement, crosswalk and authoritative
manuscript hashes. The manuscript SHA-256 remains
`8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576`.

I also read the local subsequent main-comparison final review (SHA-256
`665575c38af27592719cd5a7eaa10acad408c4ded3fd2837f426e4b77954c2ff`) as contextual
prior review. An exact-commit API request for that review path returned 404;
I do not claim that later review is in this source commit. The current application
trust chain independently binds the actual MainComparison source, its exported
interface, and the current endpoint transitive axiom audit. This distinction
does not leave an unproved theorem premise in the corollary.

## Mathematical and proof findings

I read AGENTS.md, docs/objective.md, the unchanged manuscript Section 1 setup,
`thm:main`, `eq:inversenorm`, `eq:steinsetup`, `eq:steinradial`, `cor:stein` and
its proof, and `cor:two` and its explicit map/gauge proof. I read all four new
Lean modules and both application documents in full, then traced their actual
inputs through Geometry/Statement, the Stein construction and radial/growth
proofs, MainComparison, and ExactComparisonAlgebra with its isotopy laws.

1. **Quantifiers and scope are preserved.** Both d and N range over all natural
   numbers. No positive dimension, nonempty carrier, affine-space-only carrier,
   finite-type structure, metric completeness or primitive completeness is an
   extra input. `WeaklyTames` is the nonstrict inequality for every tangent
   vector; nondegeneracy is separately supplied by the exact symplectic
   structure. The primitive is any smooth primitive satisfying the original
   symplectic/taming/inverse-growth hypotheses, with no primitive-growth or
   compact-support condition. Empty and zero-dimensional cases are not excluded.

2. **The Stein reference is actually constructed.** `steinTarget` supplies
   `SteinReferenceConstruction.reference i` before quantifying T; no reference,
   flow or comparison is requested from the caller. `constructedSteinTarget`
   fixes the same reference literally. The packaged result independently works
   for every P satisfying the original SteinReference identities. I inspected
   `reference`, `compatible`, `exactStructure`, `primitive_eq`, the native
   exterior-derivative evaluation and nondegeneracy proof, and the induced-metric
   construction from the injective differential. The primitive is a real
   ambient-form pullback, with its required identities proved. There is no
   circular geometry or output field hidden in ProperComplexEmbedding.

3. **Radius, sign and norms are literal.** R is exp(1)+norm(i.map)^2 and
   beta=-(1/4)dR composed with J. The metric is the real Euclidean inner product
   of di, equal to d beta(.,J.). `SteinRadial.reference` retains the same exact
   structure and compatible structure, chooses c=1/4 and rstar=2, and discharges
   properness, smoothness, lower bound and the radial inequality. The stronger
   estimate |dR|_g*^2 <= 4(R-e) is proved from the derivative formula and
   Cauchy-Schwarz. The new metric, dualNorm, inverseNorm and taming bridges are
   definitional equalities. Geometry's MetricTangent installs the actual g norm;
   covector keeps its original linear function with the g-dual norm;
   inverseContraction is constructed from nondegeneracy with the positive
   contraction equation. Its operator norm is g-dual to g, not a chart norm.

4. **Every admissible growth function is consumed correctly.** The original
   arbitrary B is smooth within [e,infinity), positive, dominating r, and has
   the actual interval-integral primitive tending to infinity. `extend` uses
   a smooth cutoff, equals B above e+2, and proves divergence by a finite
   additive change to that integral. `growth` supplies the real radius properness
   and lower bound to `steinRadius_growth`. The estimate retains T, g, R and C,
   enlarging the compact set only to K union {R<=e+2}; properness proves this is
   compact. No monotonicity, special growth model or global bound is substituted.

5. **The main theorem is invoked, not assumed.** `packagedSteinTarget` applies
   actual `MainComparison.mainTarget` to the constructed radial package after
   the proved growth conversion. It has no MainTarget argument.
   `comparisonWitness` exposes the actual comparisonMap/comparisonGauge at
   the literal extended B and enlarged compact set, discharging every required
   premise. I traced MainComparison's endpoint assembly and the inverse map and
   negative composition gauge; the new application does not posit a Moser flow.
   Full re-review of the previously delivered deep ODE/Cartan proofs is outside
   this bounded integration review; the present transitive audit covers their
   logical dependencies through the actual final theorems.

6. **Common-reference order and gauge agree exactly with the manuscript.**
   `commonReferenceTarget` applies actual mainTarget separately to T1 and T2,
   then the proved algebra. `explicitCommonTarget` extracts both obtained
   witnesses into its conclusion, rather than assuming them. Native
   Diffeomorph.coe_trans gives F2.symm.trans F1 = F1 composed with F2 inverse;
   the gauge is literally (h1-h2) composed with F2 inverse. I inspected Witness
   comp/symm/commonReference: the primitive identities use actual pullback and
   scalar derivative chain rules, and the exterior identities use actual
   pullback composition/inversion. The isotopy laws invert and pointwise compose
   the smooth forward/inverse families. Independent B_i, C_i, K_i are retained,
   explicitly demonstrated by separateGrowthWitnesses.

7. **Native consumers expose the full conclusion.** referenceIdentities gives
   the literal radius, primitive and induced metric. steinNativeConclusion and
   commonNativeConclusion give genuine native diffeomorphisms, smooth gauges,
   identity-start isotopies with both jointly smooth forward and inverse
   families on [0,1], the pointwise primitive identity, and the exterior-form
   pullback identity. The common consumer evaluates its endpoint explicitly
   as F1(F2 inverse x). These are conclusions obtained from the original inputs.

I inspected pinned FsFltz Smooth.lean: native Mathlib manifold/tangent spaces,
continuous alternating tangent forms, chart-transported native extDeriv,
actual mfderiv pullbacks/scalar derivatives and native Diffeomorph. I also
checked pinned Liouville.lean and FixedAmbient.lean: an object called complete
Liouville retains an actual Flow R with jointly smooth action and the chart ODE
for every real time, with i_Z d lambda=lambda. The application uses exact
symplectic terminology and infers no completeness from gauge comparison.
The proof guide accurately describes the bounded completion and its exclusions.

## Lean evidence and limits

I inspected scripts/verify-corollaries.py, its import script, Audit.lean,
source-declarations.json, names.txt, the type storage, axioms.json, receipt.json,
and all three raw managed logs. The audit enumerates the owned namespaces and
private names from the Lean environment and adds the imported interfaces. Its
prefix also covers CorollaryComparisonConsumers. All 23 source declarations are
present in the 64-name environment/interface inventory. The names, receipt,
axiom keys and type/storage keys agree exactly.

I machine-checked all 64 complete pp.all type files for expected declaration
prefixes, absence of elision, and their recorded SHA-256, and inspected relevant
elaborated binders alongside the source definitions. Alias types such as
steinTarget : SteinTarget were followed into the original definition bodies;
printing a Prop-valued specification alone was not treated as source coverage.
All three gzip files decompress successfully to the recorded complete text
hashes; stored compressed hashes also match. Their uncompressed sizes are
636674 bytes (radial_inner_eq), 805592 bytes (referenceIdentities), and 561877
bytes (commonNativeConclusion). All 64 type texts total 2656090 bytes. Compression
is storage only and removes no type information.

I reparsed the raw #print axioms output and reproduced the complete 64-entry
axiom map. The union is exactly propext, Classical.choice and Quot.sound;
no sorryAx or custom axiom appears transitively in the actual corollary,
constructed-witness or consumer exports. The four new modules have no admission,
custom axiom or unsafe declaration. This is transitive proof trust evidence,
not merely a lexical check or an audit of target proposition names.

The three serial managed checks are library build, full type/axiom audit, and
native consumer elaboration. All report returncode=0, ok=true, status=passed,
snapshot_verified=true, and source key
`9975485ba8f852aa2671ad6e8599a283dc2e1263b09954aa0efd81bc4cbe7407`.
Every raw JSON report equals its receipt entry; both completion markers are
present. The named library build replays its cached consumer job; the audit
and consumer commands elaborate their respective files. I ran no competing
managed build and do not represent this as a fresh default-root release build.
Installed dependency heads independently match FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; recorded Lean is 4.34.1.

This review is subsequent evidence: it is not in the reviewed source commit or
its earlier managed snapshot. Only this report was written into the project
by the reviewer. No further repair is required for the bounded verdict.

## Independently read-back committed SHA-256 bindings

All entries below were fetched at the exact reviewed commit and compared
byte-for-byte, including independently checking their returned Git blob hashes.
The receipt provides the exhaustive source and complete-type hash inventories;
the table records this reviewer's targeted remote readback coverage.

| Path | SHA-256 |
|---|---|
| `ExactLiouvilleComparison/CorollaryComparisonStatement.lean` | `58d21d2d38721e4e9cb3194d2ba4b4793899359cb6f3501e4ae7663651581efa` |
| `ExactLiouvilleComparison/SteinComparison.lean` | `6f1cf4fab120e3dfd1822f52776e147c02787c6472c3bc5b4c13dc739da3feb6` |
| `ExactLiouvilleComparison/CommonReferenceComparison.lean` | `163666997ab72a8595036234277101af1b44bb82d020f8c3eae2ca46c8918656` |
| `ExactLiouvilleComparison/CorollaryComparisonConsumers.lean` | `3f00b482b85f542da547766d46f535f5535da6071fe7fe8946e149e2de8e3621` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/MainComparison.lean` | `cb00802192436e1c4bd1672bfa6b56814e1a4ae776686598c909f323c992709e` |
| `ExactLiouvilleComparison/SteinReference.lean` | `c88596243053d359503ba79739f521cafb786288dfeaecde903bf4416e9e2108` |
| `ExactLiouvilleComparison/SteinRadial.lean` | `46d561e258fd8b07d84770ff70916099808f87ee6f67d61081113a8c875cd27a` |
| `ExactLiouvilleComparison/SteinGrowthConsumers.lean` | `22e51647a69577fc5694b41dc1344379905bcaf28cba58e409ff09197263cb22` |
| `ExactLiouvilleComparison/ExactComparisonAlgebra.lean` | `c15c5b615805b3c62c760c54d49c2a363c8c0c43e338c24cfa90f71248568e14` |
| `docs/corollary-comparison-crosswalk.md` | `9e2094bee96a21d5e9dac8be984eb1143ec1278d20e1d217139c28f42071bde8` |
| `docs/corollary-comparison-proof.md` | `d728c2c6461df7ee72f3b9fae37324aa1672bd1a7aa139b1bd54b0e3d6dab07d` |
| `scripts/verify-corollaries.py` | `5e514641a1eb5160c968d51b962f3f7d004de29c80aa0f8aefa492c83d002250` |
| `verification/corollaries/statement-review.md` | `8906bc829c2b315393c52d3e3688c84690c38d51891c1e1bb4480de78c12694b` |
| `verification/corollaries/statement-hashes.json` | `34469944e135936f9b126e8c50d037806eb3b0828186cc0a0d20e427127b9b84` |
| `verification/corollaries/import-manifest.json` | `eb72774c4b4c89dee03dd5ae995cc415c9f62a1ce42a2de57f22169939d937b3` |
| `verification/corollaries/Audit.lean` | `a46446565e3cc228bdf1f62c01087f7745779f6506954a822d19bb8e45dd9067` |
| `verification/corollaries/final/receipt.json` | `933f0d9843eaa5fd408c9872ce7ec95ff0a9cfa9d35a999e3bbbdf7439feea17` |
| `verification/corollaries/final/axioms.json` | `940becd4d0e0684eb18504046025c8c9ed4b04c14a51e3b1af9fa789cadb1963` |
| `verification/corollaries/final/source-declarations.json` | `b96cea560e37b71a62c1da76d4129e23026d0773af92e09baae831f7b378f1da` |
| `verification/corollaries/final/names.txt` | `4edf165b928e8e0b1b0cbc8cc37916d782458139a59a25750d78f4d2fcce721a` |
| `verification/corollaries/final/build.log` | `79bf764ed8ddfc11d8e9fa5dcb1661f0af4fea9800f6568dd692983c2ae120bc` |
| `verification/corollaries/final/audit.log` | `ef2dfd7997e813d55ae46b56355ca5a1ec438d541381faa4e2bf877a51addeea` |
| `verification/corollaries/final/consumers.log` | `ec2b3abad3d9e37dc268fb3e602643eb327048419315a09f2721aae174684085` |
| `verification/corollaries/final/types/ExactLiouvilleComparison.SteinComparison.radial_inner_eq.txt.gz` | `14491893f886daf88b0ed0107af1cd1fc5f3ed4da3a89cbf2d53854e8da93aa5` |
| `verification/corollaries/final/types/ExactLiouvilleComparison.CorollaryComparisonConsumers.referenceIdentities.txt.gz` | `17bcaaa23e6fcbbf46541b4a72db148e4cb7fab938357666463fd7e02e8532a3` |
| `verification/corollaries/final/types/ExactLiouvilleComparison.CorollaryComparisonConsumers.commonNativeConclusion.txt.gz` | `d90cb33478d3e067b98c553180e5ada32fee5e57e3ee5625d57c8ff4c996c63e` |
