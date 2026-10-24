# Independent pre-proof interface review

Mission: `226d751b-2331-4986-a5b5-fbbc2f95df01`. Reviewer: independent
`sqrt_statement_review` agent, acting as Interface Mathematician. Date: 2026-10-24.
Scope: the analytic square-root prerequisite only; normalization/bundle integration
remains with `1f45f2d4-0edc-4d6b-8646-2c1212915b09`.

Reviewed files, with independently recomputed SHA-256:

- `ExactLiouvilleComparison/CylindricalCompatibilityNormalizationSqrtStatement.lean`:
  `08336671690a328ddd69215f3e9417e5a609f445a37a1b5cf755dbba981eee0c`.
- `docs/normalization-sqrt-crosswalk.md`:
  `dbf445394cbe3e586a93f2704af10d4cd4bdb1f00ff7c90056666407f82cc215`.

**Verdict: accepted for substantive proof work. No necessary statement or crosswalk
correction identified. This is contract acceptance, not acceptance of a proof.**

The existing `statement-build.log` ends in a successful managed build with
`snapshot_verified: true`, return code zero, and source key
`ffa5f45f97ddeea89490b9e0fa5a6a6e68ebceee78b44f0a12d885abc1aefbe7`.
The preceding out-of-date-target message is followed by the successful rebuild.
I inspected this receipt and did not run a broad build.

## Definition and quantifier findings

1. `Matrix.PosDef` is actually Hermitian symmetry together with strict positivity
   of the quadratic expression on every nonzero finitely supported vector
   (`LinearAlgebra/Matrix/PosDef.lean:162`). For finite `n` this has precisely the
   advertised finite real positive-definite meaning. The contracts quantify over
   arbitrary `n` with `Fintype` and `DecidableEq`, without `Nonempty n`, and arbitrary
   real normed parameter spaces `E`; they impose no completeness on `E`.
2. The open scopes select the native matrix positive-semidefinite order, not
   entrywise order, and the Euclidean operator norm, not the default entrywise
   matrix norm. `Analysis/Matrix/Order.lean:61` identifies `0 ≤ A` with
   `A.PosSemidef`. `Analysis/CStarAlgebra/Matrix.lean:198` identifies the selected
   norm with the norm of the corresponding continuous linear map on
   `EuclideanSpace ℝ n`. Both the Sylvester equivalence and all matrix-valued
   calculus therefore use the intended operator norm. No claim identifies it with
   the manuscript's varying metric `g`; that bridge is correctly left to the parent.
3. `CFC.sqrt` is the native non-unital functional calculus applied to `NNReal.sqrt`
   (`Rpow/Basic.lean:235`), and is zero off the nonnegative locus. The imported
   Hermitian functional calculus supplies the real matrix instance. The relative
   domain in `RelativeSqrtContract` is essential in general: in matrix rank at
   least two, nonsymmetric perturbations approach a positive-definite matrix but
   have totalized square root zero. The contract correctly makes no ambient
   smoothness assertion about this totalized function.
4. `ContDiffOn ℝ ∞` is native smoothness within the set at every point in it
   (`ContDiff/Defs.lean:472`), with every finite derivative order required. The
   composition contract is meaningful for arbitrary sets: its positivity premise
   supplies exactly the `MapsTo` hypothesis of `ContDiffOn.comp`
   (`ContDiff/Comp.lean:125`). Taking `s = Set.univ` recovers globally smooth
   positive-definite families; open chart domains supply the bounded coefficient
   consumer interface. No derivative uniqueness on the positive cone is assumed.
5. `SylvesterContract` demands an actual continuous linear equivalence on **all**
   real matrices, with pointwise equality to `S * H + H * S`. This is strong enough
   to supply the derivative equivalence of ambient squaring to the inverse
   function theorem. It does not silently restrict perturbations to symmetric
   matrices, and assumes neither an inverse nor a square-root certificate.
6. `Ring.inverse` is the native inverse of a unit and zero otherwise
   (`Algebra/GroupWithZero/Units/Basic.lean:84`). Positive definiteness implies
   `IsStrictlyPositive`, hence `IsUnit (CFC.sqrt A)` by the inspected native
   `CFC.isUnit_sqrt_iff`/`IsStrictlyPositive.isUnit_cfcSqrt` results. Thus the inverse
   composition conclusion is the actual inverse square root. This implication
   must be applied in the implementation; it is not an extra assumed input.
7. Empty `n` is consistent throughout: the matrix space is a singleton, Hermitian
   symmetry holds, and there is no nonzero vector. The sole matrix is also the
   multiplicative identity, hence a unit. The Sylvester map is the unique map of
   a zero-dimensional space and is a continuous linear equivalence. All smoothness
   conclusions reduce to constant maps. The contract contains no hidden
   nontriviality premise excluding this case.

## Reuse and proof obligations

I checked the actual Mathlib definitions and theorem statements for spectral
diagonalization, positive eigenvalues, relative square-root continuity, the square
identity, the positivity/unit bridge, `ContDiffAt.to_localInverse`, and
`contDiffAt_ringInverse`. The proposed proof is mathematically sound: diagonal
Sylvester coefficients are positive sums of eigenvalues; the inverse function
theorem applies to ambient squaring; relative continuity and the square identity
identify the native square root with its local inverse along the positive cone.
This route does not require a smoothly chosen eigenbasis.

Local dependency HEADs match Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`. The inspected Mathlib matrix/CFC trees
contain no matching Sylvester or smooth-square-root theorem. Independent searches
of FsFltz and the read-only cluster source snapshot
`cluster-source-2c239b0` found no Sylvester/matrix-square-root implementation;
their square-root occurrences are scalar uses. This supports the stated reuse
order and the need for new native analytic infrastructure.

All four declarations are definitions of propositions. None establishes its
contract, and none is a circular structure field or assumed theorem. Proof
delivery still requires actual inhabitants without forbidden axioms, an exact
source build and transitive axiom audit, plus compiled consumers including empty
rank and smooth positive-definite families. Bundle gluing, coordinate/metric
identification, normalization algebra, and the manuscript theorem are outside
this review and remain unproved by these contracts.
