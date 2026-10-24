# Independent pre-proof definition and statement review

Reviewer: independent `contract_review` agent, 2026-10-24.
Mission: 30bfbe32-1f63-42e8-8279-88f994bffb09 revision 1.
Verdict: **APPROVED as an algebraic construction definition and three proof targets.**
No semantic correction is required before substantive algebra proof work.
This is not approval of completed proofs, smooth dependence, tangent-bundle
assembly, the compatible extension, or the main comparison theorem.

## Exact reviewed inputs

SHA-256:

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/CylindricalCompatibilityNormalizationAlgebraStatement.lean` | `9089c2951c21eaa757f5a739bb1f6d976512c659855706638832896f64b26ecc` |
| `docs/normalization-algebra-crosswalk.md` | `6f92381c2f2c08bfb3bb1dfc357b46bff764f334fad1afa4fb9013a10976d56a` |
| `verification/normalization-algebra/statement-build.json` | `2b7bd69d87e44cdf8e5e17067fb9f9da097bb294f43432beb1d7a6a1571c1c14` |

The supplied receipt records successful source-verified compilation of this
statement module, with source key
`b69cd626ffaffe366dce967460963d3d9b51ee1eede60f672d8dabab24eae0ec`.
I read that receipt; I did not independently rerun a build or an axiom audit.
The receipt's source key is an engine fingerprint, not the source-file SHA-256.

I read `AGENTS.md`, `docs/objective.md`, and the unchanged reference manuscript.
The immediate source locator is the compatible-extension assertion immediately
before `cor:liouville`, with the compatibility and metric convention in the
opening comparison setup. The algebraic normalization is a supporting
construction for that assertion, not a restatement of the entire corollary.

## Meaning of the definitions and targets

All indices are `Fin n`, with `n` universally quantified over every natural
number. `Mat n` and `Vec n` are literal Mathlib matrices and coordinate vectors.
`form` abbreviates the native linear equivalence `Matrix.toBilin'`, evaluated as
`v dot (W *v w)`. Thus it is the bilinear form `vᵀ W w`, with the second
argument multiplied by `W`. No custom form evaluator or arbitrary operation
replaces this mathematical object.

`Matrix.PosDef` unfolds to Hermitian symmetry and strict positivity on nonzero
finitely supported vectors. At these finite real indices,
`Matrix.posDef_iff_dotProduct_mulVec` identifies it with symmetry and
`vᵀ G v > 0` for every nonzero coordinate vector. The star on real scalars is
trivial. The metric is therefore explicitly `form G`, with no implicit use of
the coordinate sup norm. There are no dual norms, operator norms, or estimates
in these targets.

`W.transpose = -W` gives alternation over the real field, and `IsUnit W` is
ordinary invertibility in the square matrix ring. `normalize` takes only `G`
and `W`; it contains no proof fields, compatibility witness, assumed positive
root witness, or conclusion certificate. Both inverse operations are native
total matrix inverses. Their correct use on admissible inputs must be justified
in the proofs. `metricRoot` and `polarRoot` use actual `CFC.sqrt`.

`NormalizationContract` says that every positive-definite metric and invertible
skew-symmetric matrix yield, by the literal formula, an endomorphism squaring
to minus identity, preserving `W`, and satisfying `W(v,Jv)>0` off zero.
`RecoveryContract` says the formula recovers every given compatible `J₀`
when its induced metric is exactly `G=W*J₀`.
`NaturalityContract` transforms both input tensors by `Pᵀ(-)P` for every
invertible `P`, and transforms the output by `P⁻¹(-)P`. No orthogonality,
orientation, positive determinant, positive rank, or chosen complex structure
is hidden in that hypothesis list. Each declaration is explicitly a `Prop`
definition; none constitutes a theorem proving that proposition.

## Formula, sign, and boundary checks

Write `H=sqrt(G)`, `K=-H⁻¹ W H⁻¹`, and `Q=sqrt(-K²)`.
The associated operator convention `g(Av,w)=omega(v,w)` gives
`AᵀG=W` and hence `A=-G⁻¹W`. Whitening therefore gives `K=HAH⁻¹`.
The definition `J=H⁻¹KQ⁻¹H` has the correct sign. In dimension two,
`G=1` and `W=[[0,1],[-1,0]]` give `J=-W` and `WJ=1`.

The expected proof mechanism is mathematically sound: skew symmetry makes
`-K²=KᵀK` positive definite, and root identities and commutation give
`J²=-1` and `WJ=HQH`, positive definite. These identities also imply form
preservation. This analysis checks the target; the Lean identities still need
proof and must not be added as construction assumptions.

For recovery, `G=WJ₀` and `J₀²=-1` imply `A=J₀`, so the whitened operator
squares to `-1`; its positive polar root is the identity. The intended fixed
point behavior follows. Thus this is a genuine recovery condition, without
an assumption equating the result to the desired output.

For naturality, let `H'=sqrt(PᵀGP)` and `U=HP(H')⁻¹`. Then `UᵀU=1`,
`K'=UᵀKU`, and positive-root uniqueness gives `Q'=UᵀQU`. Substitution gives
exactly `J'=P⁻¹JP`. An arbitrary `P` cannot be treated directly as a star
equivalence, and the crosswalk correctly uses the intervening orthogonal `U`.

At `n=0`, both vector and matrix types are subsingletons; zero equals identity
in the matrix ring. The sole matrix is a unit, positive definiteness has
vacuous strict-positivity clause, and every matrix equality in the targets
holds. The CFC matrix instance inspected below assumes `Fintype` and
`DecidableEq`, not `Nonempty`. Thus zero rank is genuinely covered by the
definitions, including recovery and naturality. In odd positive dimension
there is no invertible real skew-symmetric input; that mathematical absence
does not remove any requested admissible input. Positive even dimensions give
nonvacuous instances, including the two-dimensional example above.

## Native interfaces inspected and remaining bridges

I verified the checked-out dependency commits by `git rev-parse HEAD`:
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`.

Inspected actual declarations include:

- `Matrix.toBilin'`, `Matrix.toBilin'_apply'`, and
  `Matrix.nondegenerate_toBilin'_iff` in `LinearAlgebra/Matrix/BilinearForm`.
- `Matrix.PosDef`, `Matrix.posDef_iff_dotProduct_mulVec`, and
  `Matrix.PosDef.isUnit` in `LinearAlgebra/Matrix/PosDef`.
- `Matrix.mulVec_injective_iff_isUnit` and
  `Matrix.isUnit_iff_isUnit_det` in `LinearAlgebra/Matrix/NonsingularInverse`.
- The scoped `MatrixOrder` order, `nonneg_iff_posSemidef`, and
  `isStrictlyPositive_iff_posDef` in `Analysis/Matrix/Order`.
- The actual real-matrix CFC instance in
  `Analysis/Matrix/HermitianFunctionalCalculus`, and the definition
  `CFC.sqrt a = cfcₙ NNReal.sqrt a`, `sqrt_mul_sqrt_self`, `sqrt_unique`, and
  `isUnit_sqrt_iff` in `Rpow/Basic`.
- `AlmostComplexField` and the full definition `IsCompatibleAlmostComplex`
  in FsFltz `Geometry/Maslov`: it uses native tangent continuous linear maps,
  chart smoothness, pointwise square-minus-identity, preservation of the
  actual two-form, and strict positivity. The three algebraic clauses match
  the present `Compatible` after evaluation bridges; its smoothness clause
  is deliberately outside this mission.
- FsFltz `CompatibleComplexTransport` and `CompatibleComplexPath`: these
  consume already compatible structures and do not supply the present
  metric-to-compatible-structure construction.

The implementation should prove the advertised alternation and nondegeneracy
bridges and the equivalence between matrix compatibility and the corresponding
pointwise native bilinear/linear-map conditions. Ordinary basis transport
then has a clear destination; arbitrary-GL naturality is the necessary
coordinate-independence consumer. Actual continuous-linear-map realization,
smoothness, and tangent-bundle gluing must be discharged by the corresponding
owners before claiming a smooth native almost complex field. Their absence
from this algebraic statement is an explicit scope boundary, not a hidden
hypothesis or a completed construction.

The required cluster archive search was independently repeated in
`/var/lib/archon-worker/imports/project-reference/archon_liouville/cluster-source-2c239b0/Hu-Mingyuan-cluster-skeleton-2c239b0c03922a1549f18ee3a45a8e0ca25bb28c/ClusterSkeleton`.
The patterns `CFC.sqrt`, `PosDef`, `polarDecomp`, `compatibleComplex`, and
`IsCompatibleAlmost` returned no matches in its Lean sources. During review,
the owner expanded the crosswalk's archive path to the full extraction suffix.
I inspected that documentation-only correction; the hash above records it.

## Acceptance boundary

There is no blocking definition or statement defect. The native matrix
representation is appropriate for the finite algebra mission, and the
crosswalk correctly distinguishes it from the later manifold construction.
No source, manuscript, or dependency was changed in this review.

This review authorizes starting proofs of the exact targets; it does not
certify those proofs or their transitive axioms. Final acceptance still needs
the actual compatibility, recovery, naturality and bridge proofs, reproducible
exact-source compilation, appropriate consumers, and the required foundational
axiom audit. A successful build of target propositions alone supplies none of
those mathematical conclusions.
