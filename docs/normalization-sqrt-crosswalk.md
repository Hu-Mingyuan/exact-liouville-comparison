# Positive matrix square root: analytic contract

Mission 226d751b-2331-4986-a5b5-fbbc2f95df01, revision 1. Integration remains with
normalization assignment 1f45f2d4-0edc-4d6b-8646-2c1212915b09. This prerequisite
does not construct a symplectic normalization or glue bundles.

The statement module is `CylindricalCompatibilityNormalizationSqrtStatement.lean`.
Its four named propositions are contracts, not established theorems or input
certificate fields. They will not be assumed by the delivered square-root proof.

| Mathematical object | Pinned native definition and meaning |
| --- | --- |
| Real matrices, any finite rank | `Matrix n n ℝ`, `[Fintype n] [DecidableEq n]`; no `Nonempty n` |
| Positive definite | `Matrix.PosDef`: Hermitian and strictly positive quadratic form on every nonzero vector |
| Matrix norm | `Matrix.Norms.L2Operator`: operator norm for the standard Euclidean inner product on `EuclideanSpace ℝ n`; not an assertion about the manuscript's manifold metric |
| Positive square root | `CFC.sqrt` with `MatrixOrder`, native real Hermitian matrix functional calculus from `Analysis.Matrix.HermitianFunctionalCalculus` |
| Regularity | `ContDiffOn ℝ ∞`, Fréchet smoothness within the supplied set at each of its points |
| Sylvester inverse | actual native `ContinuousLinearEquiv` on the whole real matrix space, acting as `H ↦ S*H+H*S` |
| Inverse square root | native `Ring.inverse` of the positive square root, whose unit property must be proved |

For empty `n`, the matrix space has one element and positivity is vacuous. All
contracts retain this case. No arbitrary operation replaces matrix multiplication,
order, the square root, topology, or derivatives. No manifold metric, dual norm,
Liouville data, or flow occurs in this bounded analytic result. Bundle consumers
must separately identify their coordinates and metric; that is the parent's scope.

The relative domain is essential: `CFC.sqrt` is totalized outside the nonnegative
locus, so ambient smoothness at positive matrices is not claimed. A smooth family
mapping its domain into positive-definite matrices is covered by composition of
the relative theorem. Taking the domain to be `Set.univ` gives global composition;
open chart domains give the intended local bundle coefficient interface.

Reuse audit (pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612,
FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb, cluster 2c239b0c03922a1549f18ee3a45a8e0ca25bb28c):
Mathlib supplies `Matrix.IsHermitian.spectral_theorem`, `Matrix.PosDef.eigenvalues_pos`,
`Matrix.isStrictlyPositive_iff_posDef`, `CFC.continuousOn_sqrt`,
`CFC.sqrt_mul_sqrt_self`, `CFC.isUnit_sqrt_iff`, and `ContDiffAt.to_localInverse`.
The square-root continuity theorem is relative to nonnegative elements. The
inverse-function theorem requires a proved derivative continuous linear equivalence.
Searches of FsFltz and the read-only previous cluster source found scalar square-root
uses but no smooth matrix-square-root or Sylvester inverse theorem. Thus new proof
infrastructure is needed, using native Mathlib operations throughout.

Planned proof: diagonalize a positive-definite square root; in eigen-coordinates
the Sylvester operator multiplies entry `(i,j)` by the positive number `d i + d j`.
Prove its bijectivity and obtain a continuous linear equivalence in finite dimension.
Apply the inverse function theorem to squaring. Relative continuity of `CFC.sqrt`
and its squaring identity identify it with this smooth local inverse along the cone.
Then compose with the supplied family and apply native inverse calculus for units.
