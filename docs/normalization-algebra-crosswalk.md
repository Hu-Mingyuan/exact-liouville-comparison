# Metric symplectic normalization algebra: definition crosswalk

Scope: mission 30bfbe32-1f63-42e8-8279-88f994bffb09 revision 1, within
roadmap 86760810-08b9-4687-a4a9-37f6a45e361c revision 1, source
f8b5b6bcb56a18c0094d15fed4619ff100327e30:docs/sdu-continuation.md.
This is the finite-dimensional algebra needed for the compatible extension
asserted before manuscript corollary `cor:liouville`. It proves neither
smooth dependence nor native bundle assembly; those remain with the named
analytic sibling and parent normalization owner.

The auxiliary module is
`ExactLiouvilleComparison/CylindricalCompatibilityNormalizationAlgebraStatement.lean`,
namespace `ExactLiouvilleComparison.NormalizationAlgebra`. Contract propositions
are proof obligations, not theorems and never input fields of the construction.

| Mathematics | Actual representation and convention |
| --- | --- |
| Arbitrary finite dimension | `Mat n = Matrix (Fin n) (Fin n) ℝ`, every `n : ℕ`, including zero; no `Nonempty (Fin n)` assumption |
| Vectors | `Vec n = Fin n → ℝ`, matrices act on column vectors via native `Matrix.mulVec` |
| Metric | Native `Matrix.PosDef G`; metric is `form G v w`, not the coordinate sup norm |
| Bilinear form | `form W = Matrix.toBilin' W`, native `LinearMap.BilinForm`; `Matrix.toBilin'_apply'` gives `v ⬝ᵥ W *ᵥ w` |
| Alternation | `W.transpose = -W`; a bridge to vanishing diagonal evaluations will be proved |
| Nondegeneracy | `IsUnit W`; bridges use native `Matrix.mulVec_injective_iff_isUnit` and native bilinear nondegeneracy |
| Associated operator | `g (A v) w = omega v w` gives `Aᵀ G = W`, hence `A = -G⁻¹ W` |
| Whitening | `H = metricRoot G = CFC.sqrt G`, `K = skew G W = -H⁻¹ W H⁻¹`; prove equivalence with `H A H⁻¹` |
| Positive root | `Q = polarRoot G W = CFC.sqrt (-(K*K))`; positivity/invertibility and `Q*Q=-(K*K)` must be proved, not assumed |
| Normalization | Literal `H⁻¹ K Q⁻¹ H`; all operations are Mathlib matrix operations |
| Compatibility | `J*J=-1`, `Jᵀ W J=W`, and `form W v (J*ᵥv)>0` for every nonzero vector |
| Recovery | Given compatible `J₀` and `G=W*J₀`, prove the literal formula equals `J₀` |
| Coordinates | `v_old=P v_new`, `pull P G=Pᵀ G P`, `pull P W=Pᵀ W P`, and `J_new=P⁻¹ J_old P`, for every `IsUnit P` |

The formula's minus sign is essential: for the usual two-dimensional form
`W = [[0,1],[-1,0]]` and `G=1`, the positive compatible structure is `J=-W`.
Rank zero is retained with its zero vector space, vacuous strict positivity and
unique endomorphism (identity equals zero). No positive-determinant restriction
on coordinate changes is imposed.

There are no norm estimates in this algebraic mission. The metric is explicit
as a bilinear form. If later consumers introduce tangent, dual or operator
norms they must use this metric, not silently substitute the coordinate norm.

## Reuse inspection

Pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612:
`Analysis.Matrix.Order` supplies the scoped `MatrixOrder` order, actual real
matrix CFC instances, `Matrix.nonneg_iff_posSemidef`,
`Matrix.isStrictlyPositive_iff_posDef`, and positive-root APIs imported from
`Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`:
`CFC.sqrt_mul_sqrt_self`, `CFC.sqrt_unique`, `CFC.isUnit_sqrt_iff`.
`LinearAlgebra.Matrix.BilinearForm` supplies the native form representation.
`LinearAlgebra.Matrix.PosDef` supplies positivity and invertibility.
`Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute` supplies commutation.
No arbitrary real-Hilbert-endomorphism CFC instance is assumed.

Pinned FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb:
`Geometry/CompatibleComplexTransport.lean` and `CompatibleComplexPath.lean`
start with already compatible structures. They do not construct one from a
metric and alternating form, so they do not discharge this prerequisite.

Mandatory third search inspected the read-only cluster-skeleton archive at
`/var/lib/archon-worker/imports/project-reference/archon_liouville/cluster-source-2c239b0/Hu-Mingyuan-cluster-skeleton-2c239b0c03922a1549f18ee3a45a8e0ca25bb28c/`
(commit 2c239b0c03922a1549f18ee3a45a8e0ca25bb28c). Searches for `CFC.sqrt`,
`PosDef`, `polarDecomp`, `compatibleComplex`, `IsCompatibleAlmost` in its
`ClusterSkeleton` Lean sources found no normalization implementation.
No upstream or authoritative manuscript file is changed.

## Proof plan and status

First establish native form bridges and square-root/whitening identities.
Prove compatibility in Euclidean coordinates, then conjugate back. For arbitrary
coordinate changes use `U = sqrt(G) P sqrt(Pᵀ G P)⁻¹`, which is orthogonal;
prove square-root transport using positivity and `CFC.sqrt_unique`. An arbitrary
`P` is not treated as a star equivalence. Recovery follows from `A=J₀` and
`A²=-1`, making the metric polar root the identity.

Pre-proof status: construction definitions and target propositions only.
No compatibility, recovery or naturality proof has yet been claimed.
Independent review must precede substantive proof work.
