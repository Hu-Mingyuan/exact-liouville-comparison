# Independent bounded proof review

Reviewer: native helper `/root/ode_proof_review`, Astra/high, 2026-10-23.
The helper was collected before parent completion. Read-only advisory review;
not a formal PR approval or mission/phase acceptance.

**Assessment: PASS for the bounded mathematical proof**, conditional on exact
compilation and the transitive axiom audit, supplied separately by `receipt.json`.
No blocking definition error, extra hypothesis, assumed flow, circular
continuation argument, or endpoint/both-direction defect was found.

Final reviewed source SHA-256:

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/ODEContinuationCutoff.lean` | `7371c5defeccd22af52bf034cd66aacb642d2181da2ef1d49e62cf5cccc4e80b` |
| `ExactLiouvilleComparison/ODEContinuation.lean` | `23f47f09944ddff65928949fe7385226a2e7b3b274dda87396eec8b155de9927` |
| `ExactLiouvilleComparison/ODEContinuationStatement.lean` | `d1f8ad17b89f7acea0a9c757319bcfc027666df264c9471ba01d0c03164598f1` |
| `ExactLiouvilleComparison/ODEScalarConfinement.lean` | `0b07b6c8765cb2cbe1a81407ec1f051f80fd9d3f5003fe711a99e2c708083fa8` |
| `verification/ode-continuation/crosswalk.md` | `eb61aa6912629230295407c5413e7ab9c622ca21b923bd46d1440420749babca` |
| FsFltz `Geometry/CollarEvolution.lean` | `162ec4959c8d51f82c8bb6c59dff9074a84abf98dde4978d256d1851c1eaa361` |
| FsFltz `Geometry/FamilyLiouvilleLocalFlow.lean` | `9147a497dcc88e6264683c37fbe0677f8852c8de6a6fbd940f502637866e4df5` |
| Mathlib `Geometry/Manifold/PartitionOfUnity.lean` | `84af32092e72da67d512308c6d18c30a455033cba577ac5da69113c0c29910ae` |
| Mathlib `Geometry/Manifold/VectorBundle/ContMDiffSection.lean` | `8204881474914aec527bba10f1339f0173152031fd712eb6048425dd2f63e06f` |

## Findings

Properness and boundedness below make the chosen sublevel compact. The actual
Mathlib cutoff theorem supplies its range [0,1], retained in the new lemma.
Linearity of the native scalar derivative then preserves the uniform strip
bound after multiplication. The product tangent-bundle equivalence and native
supported-section multiplication prove global smoothness even when the
original field behaves arbitrarily outside Ω.

The reviewer inspected FsFltz `CollarFlow.exists_global_solution`: it constructs
all-real solutions from compact spacetime support, proves uniform local
lifetime for its speed-one suspension, applies native continuation, and
identifies the time coordinate by uniqueness. It assumes no flow or
continuation certificate. The zero time component in the section-extension
bridge is not used as the ODE suspension.

The scalar displacement inequality is symmetric in terminal and initial time.
The bound |t-s| ≤ 1 keeps the auxiliary curve in K for all closed-interval times,
where the cutoff equals one. Substitution in the full native auxiliary ODE
therefore proves full `HasMFDerivAt` at 0 and 1 as well as the interior.
No scalar bound outside [0,1] or metric completeness assumption is introduced.

`M.Tangent` is native `TangentSpace`; `scalarDerivative` is actual `mfderiv`
evaluation. Manifold separation, countability, smoothness and finite model
dimension are supplied by the unchanged `SmoothManifold` interface. The
reviewer found no admission, custom axiom or unsafe proof operation in the
inspected sources; declaration-level transitive auditing remains a separate
kernel check.

The helper re-read the final compilation repairs: the upstream cutoff's
regularity parameter is `(n := ⊤)`, an unused boundaryless assumption was
removed from the general auxiliary cutoff lemma, model/field arguments were
made explicit, and W was unfolded in two simplifications. These preserve the
proof meaning. The crosswalk and proof explanation were reviewed as accurate.
The documentation's status wording was subsequently updated to reflect the
successful managed build, without changing the argument or claimed scope.

The reviewer performed no builds, edits or API operations, and did not
independently verify repository/API provenance. The parent owns the exact-source
receipts and publication. This review establishes neither smooth evolution nor
full first-path/comparison acceptance.
