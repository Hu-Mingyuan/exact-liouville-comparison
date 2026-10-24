# Independent review: degenerate normalization cases

Mission: `50754190-03fe-44b3-830e-5b109eca0470`.
Reviewer: independent `normalization_statement_review` agent.
Decision: **ACCEPT the four degenerate-case proofs and their recorded partial
verification.** This is not acceptance of general normalization or the mission.

## Exact reviewed artifacts

| Artifact | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/CylindricalCompatibilityNormalizationDegenerate.lean` | `b4f30b3daeeda2d3c4069166b8589796243c49126aed3777f917d8a5db8f8cdb` |
| `ExactLiouvilleComparison/CylindricalCompatibilityNormalizationChecks.lean` | `754bbc49bacfd791f07ef0eaa67087642963d9dd70a7b370a1b2817d3a7a6f75` |
| `scripts/verify-cylindrical-compatibility-normalization.py` | `51c68857f412d2817ae0c7c55a842fe8a45789bfd5430f155569336ef3644a15` |
| `verification/cylindrical-compatibility-normalization/partial-receipt.json` | `d338b4d48c4c721578183747f322929a78e88f4be3f41a9e19f41b84960c1697` |
| Previously accepted statement | `a100611cd3ccc7a9076e318f3b4fc8e376f1dd9e1fc304004e4adec270ec2fc3` |
| Previously accepted crosswalk | `3c009a3a5bbd22219fff51ac1b6e3ed5140d057b9e3c48d95c74e0a1f8ab906c` |

The statement and crosswalk remain the accepted repaired contract. All source
hashes listed in `partial-receipt.json` were independently recomputed and match
the present files, including the unchanged manuscript and dependency manifest.

## Proof findings

1. `normalization_of_isEmpty` constructs the actual zero endomorphism section.
   Its smoothness is Mathlib's `contMDiff_zeroSection` instantiated for the
   native endomorphism bundle. Compatibility and recovery eliminate an actual
   hypothetical point of the empty base. There is no nonemptiness assumption
   hidden in the construction and no substitute target proposition.
2. `normalization_of_subsingleton_fibers` also constructs the actual zero
   section. The square identity holds because all fiber vectors coincide;
   invariance reduces by the genuine bilinear map laws; off-zero positivity
   follows because a nonzero vector cannot exist. Recovery proves equality of
   continuous linear maps by extensionality into the subsingleton fiber. It
   does not drop or weaken the recovery clause of `NormalizationTarget`.
3. `normalization_of_subsingleton_model` derives each fiber's subsingleton
   instance from the injectivity of
   `(trivializationAt F E x).linearEquivAt ℝ x
   (mem_baseSet_trivializationAt F E x)`. The inspected pinned definition is
   an actual linear equivalence `E x ≃ₗ[ℝ] F` at a point in the trivialization's
   base set. Thus this is a proved native-bundle bridge, not an assumption
   identifying every fiber with F. It works on an arbitrary base.
4. `normalization_of_finrank_zero` uses `Module.finrank_zero_iff` and then the
   model bridge. The inspected Mathlib theorem requires a finite module;
   the retained `FiniteDimensional ℝ F` supplies it. Consequently this does
   not accidentally interpret the natural-number `finrank` of an infinite
   dimensional space as a legitimate zero-rank case.

All four conclusions are the original `NormalizationTarget IB F E omega h`
with the supplied form and metric unchanged. Their section parameters occur
in that target, so the repaired finite-rank/smoothness assumptions remain
present. The proofs use no normalization theorem as a premise and contain no
admissions or custom axioms. Their lack of positive-rank content is deliberate
and accurately documented.

Mathlib's `contMDiff_zeroSection` was inspected in
`Geometry/Manifold/VectorBundle/Basic.lean`: it proves native section smoothness
using the local trivialization criterion and the zero coefficients. No
unproved chart-gluing or spectral-smoothness step enters these special cases.
The rank theorem was inspected in `LinearAlgebra/Dimension/Finite.lean`, and
the fiber equivalence in `Topology/VectorBundle/Basic.lean`, at the previously
verified Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Verification and script assessment

The recorded build and audit both succeeded under Lean 4.34.1 with
`snapshot_verified=true` and the same source key:
`14d95259e89d9080a6b24e1a9ae26d41cc5588ecb1feeffa9e70a2199c993864`.
The raw `partial-build.txt` and `partial-audit.txt` agree with the receipt.
No additional build was needed for this review.

`Checks.lean` imports the proved module, prints the actual target closure, and
requests transitive axiom reports for all four theorems and the three contract
declarations. The printed closure retains the three previously repaired
hypotheses. All seven reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. This is a theorem-level audit for the four special cases, not
merely an audit of their target proposition.

The script invokes managed build and audit, rejects unsuccessful or
source-unverified responses, requires every named axiom report, rejects any
axiom outside the allowed set, and writes scoped receipts. Its scope text
explicitly leaves positive-rank normalization open. One automation limitation
is nonblocking for this reviewed run: hashes are collected after the checks,
and the script does not itself enforce matching build/audit source keys or
hash stability across the two invocations. Here the keys agree and all recorded
hashes match by independent inspection; future changing-worktree runs must
check these facts again or strengthen that guard. The script also assumes the
managed checker is installed; it is not yet standalone final-project CI.

## Limits

Acceptance is confined to the empty-base and rank-zero branches. It does not
prove positive-rank polar normalization, smooth square roots, naturality,
metric gluing, cylindrical extension, or the final comparison theorem. The
previous statement review's native form/metric consumer bridges remain open
until separately implemented and reviewed. These special-case results may be
used by the forthcoming algebraic and analytic work without treating them as
completion of the general construction.
