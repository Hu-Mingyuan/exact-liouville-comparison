# Independent final review: real matrix square-root prerequisite

Mission: `226d751b-2331-4986-a5b5-fbbc2f95df01`. Reviewer: independent
`sqrt_statement_review` agent, acting as Interface Mathematician. Date: 2026-10-24.
Reviewed private source commit: `cbcb67442012a4e670755eaca9ad0dfc20656484`.

**Verdict: accepted for the bounded analytic mission. No necessary mathematical,
proof, or API corrections remain.** The four previously reviewed contracts now
have actual proofs. This verdict does not accept bundle normalization, gluing,
or the full Liouville comparison theorem.

## Reviewed source identity

Independently recomputed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `CylindricalCompatibilityNormalizationSqrtStatement.lean` | `08336671690a328ddd69215f3e9417e5a609f445a37a1b5cf755dbba981eee0c` |
| `CylindricalCompatibilityNormalizationSqrtSylvester.lean` | `4686019828e4507f4951302bae0d6202fb203c1ad90dd9ed27e15fd28fca5583` |
| `CylindricalCompatibilityNormalizationSqrt.lean` | `8e8aa4a0f2c6e4384d1390cb099df0994c41366a754884abcfd30719b23a24d0` |
| `docs/normalization-sqrt-crosswalk.md` | `dbf445394cbe3e586a93f2704af10d4cd4bdb1f00ff7c90056666407f82cc215` |
| `docs/normalization-sqrt-proof.md` | `f18ff296e8f00797a55d2e0a43e962cebb66ef224be50e3b801771c28c8a3aa2` |

The three Lean files are under `ExactLiouvilleComparison/`. The statement and
crosswalk retain their pre-proof reviewed hashes. I also matched every one of the
11 source hashes in both verification receipts, including the consumer, audit,
type-report input, verification script, and earlier independent review.

## Mathematical and API findings

- **Sylvester equivalence:** `sylvester` uses native continuous left and right
  multiplication on the whole real matrix space. The kernel proof conjugates by
  the native spectral unitary and obtains entrywise multiplication by the strictly
  positive sum of two eigenvalues. It requires no symmetry of the unknown matrix
  and no smoothly chosen eigenbasis. `LinearEquiv.ofInjectiveEndo` supplies
  surjectivity in finite dimension; `toContinuousLinearEquiv` supplies an actual
  continuous inverse. `sylvesterEquiv_apply` identifies the equivalence with
  `H ↦ S * H + H * S`, and `hasFDerivAt_sq` proves the derivative of squaring using
  native multiplication calculus.
- **Relative square-root smoothness:** native strict positivity of `CFC.sqrt A`
  and its square identity justify applying the inverse function theorem to
  ambient squaring at the square root. The proof pulls the local left-inverse
  identity back using `ContinuousWithinAt CFC.sqrt` on the positive-definite
  cone, then substitutes the square identity for nearby positive-definite
  matrices. Eventual equality within that cone transfers smoothness. The
  point-membership premise of `congr_of_eventuallyEq_of_mem` is supplied. This
  establishes precisely relative `ContDiffOn`, without asserting the false
  general ambient smoothness claim for the totalized native square root.
- **Composition and inversion:** `ContDiffOn.comp` consumes precisely the given
  smoothness and positivity hypotheses on an arbitrary parameter subset. The
  inverse theorem proves the square root is a unit, extracts that unit, and uses
  `contDiffAt_ringInverse`; it does not assume an inverse or its regularity.
  Global variants follow by taking the parameter set to be universal.
- **Quantifiers, norms, and rank:** the elaborated types have no `Nonempty n`,
  no completeness assumption on the parameter space, and no certificate input
  carrying a desired conclusion. The scopes continue to select native matrix
  positivity and the Euclidean operator norm. Empty rank is retained by the
  spectral entrywise argument, finite-dimensional equivalence, and native CFC
  and calculus instances. Explicit `Fin 0` square-root, inverse-square-root, and
  Sylvester consumers compile.
- **Consumer adequacy:** the compiled consumer proves smoothness for the
  polynomial family `(t² + 1) • 1`, its inverse square root, arbitrary subsets,
  and the equation solved by the full Sylvester inverse. Together with the
  universally quantified elaborated types, these demonstrate the requested
  coefficient-family API. Coordinate naturality and identification with varying
  bundle metrics remain correctly assigned to the normalization owner.

The proof guide accurately describes the implementation. The native supporting
definitions and lemmas, including the inverse function theorem's eventual
left-inverse identity, the within-set congruence theorem, and the finite-dimensional
injective-endomorphism construction, were inspected directly. No circular field,
assumed square-root regularity, replacement operation, or unproved bridge is used.

## Verification and exact-commit evidence

I inspected the verification script, source inventory, elaborated types, consumer,
raw managed logs, and transitive axiom audit. All 19 declarations are accounted
for; their reported transitive axioms are only `propext`, `Classical.choice`, and
`Quot.sound`. There is no `sorry`, `admit`, custom axiom, or unsafe proof shortcut
in the reviewed implementation. Initial verification has four successful managed
checks at source key
`b5cd74b811775347bf43017f12de847bc8462ba91b5285cb179fe5324c17dd81`.

`publication.json` records the private commit's verified tree delta over base
`f8b5b6bcb56a18c0094d15fed4619ff100327e30`, preservation of unchanged entries, and
exact-commit API readback of all 18 published paths. I independently matched all
18 reported SHA-256 values and Git blob OIDs to the reviewed files. Publication
itself does not claim Lean validation.

The separate exact-source materialization was constructed from that clean base
and the exact-commit API readbacks, reusing pinned dependency packages. Its local
Git HEAD remains the base commit; this review does not claim a direct checkout
of the published commit. I independently checked all 11 source hashes in that
materialization against the reviewed files and inspected `exact-receipt.json`
and all four `exact-*.log` files. Build, elaborated types, audit, and consumers
all pass with `snapshot_verified: true` and common source key
`cbe0b17fa0b7186b9c65cc3f521b854e2e05a29ccc45fbd88efbe20b262965f1`.
The 19 decoded types match the reviewed type report, and the repeated 19 axiom
reports contain only the permitted axioms. These are managed, source-verified
checks using available caches, not a claim of rebuilding all dependencies from
scratch. I did not perform a redundant broad build.

This acceptance may carry forward to a documentation/evidence-only successor
that adds this review and the exact-check evidence while preserving the reviewed
Lean sources, interfaces, dependency pins, and source hashes. Such a successor
must not be described as a new proof review of changed sources. No GitHub upload
or final project packaging is accepted or implied here. The parent normalization
mission `1f45f2d4-0edc-4d6b-8646-2c1212915b09` retains its outstanding geometry work.
