# Smooth positive-definite real matrix square root

The delivered Lean entry point is
`ExactLiouvilleComparison.CylindricalCompatibilityNormalizationSqrt`.
All declarations lie in `ExactLiouvilleComparison.NormalizationSqrt`.
The independent pre-proof review is in
`verification/normalization-sqrt/statement-review.md`; the reviewed contract and
crosswalk remain unchanged. This result is the analytic prerequisite only.

## Public interface

For any finite type `n`, with decidable equality and **without** a nonempty
assumption, `contDiffOn_sqrt_posDef` proves native `ContDiffOn ℝ ∞ CFC.sqrt`
on `{A : Matrix n n ℝ | A.PosDef}`. Importers should open the scopes
`MatrixOrder Matrix.Norms.L2Operator ContDiff` to use the intended matrix
order, Euclidean operator norm and smoothness notation.

For any real normed parameter space `E`, subset `s`, family `f`, smoothness
`ContDiffOn ℝ ∞ f s`, and positivity `∀ x ∈ s, (f x).PosDef`:

- `contDiffOn_sqrt_comp` proves smoothness of `x ↦ CFC.sqrt (f x)` on `s`.
- `contDiffOn_inverse_sqrt_comp` proves smoothness of
  `x ↦ Ring.inverse (CFC.sqrt (f x))` on `s`.
- `contDiff_sqrt_comp` and `contDiff_inverse_sqrt_comp` give global versions.

No completeness of `E`, smooth eigenbasis, smoothness certificate for the square
root, or assumed inverse is an input. Local chart coefficient families use the
arbitrary-set interface. Parent normalization assignment
`1f45f2d4-0edc-4d6b-8646-2c1212915b09` retains coordinate naturality, the relation
to bundle metrics, normalization algebra, and bundle assembly.

## Proof

`sylvester` is the sum of native continuous left and right multiplication maps.
`sylvester_injective` conjugates a kernel equation by the spectral unitary of a
positive-definite real matrix `S`. Its `(i,j)` entry becomes
`(d i + d j) * H' i j = 0`. Both eigenvalues are positive, so every entry of `H'`
vanishes. Conjugation is injective, so the original matrix vanishes.
`LinearEquiv.ofInjectiveEndo` supplies surjectivity in finite dimension and
`toContinuousLinearEquiv` supplies continuity of both directions. Thus
`sylvesterEquiv` is an actual equivalence on the entire real matrix space.
`hasFDerivAt_sq` identifies it with the derivative of squaring.

For positive-definite `A`, native functional calculus proves that `S = CFC.sqrt A`
is positive definite and `S*S = A`. Squaring is smooth on the ambient matrix
space and has derivative `sylvesterEquiv` at `S`. The native inverse-function
theorem supplies a smooth local inverse at `A`.

`CFC.continuousOn_sqrt` gives continuity within the nonnegative cone. Restricted
to the positive-definite cone, this makes `sqrt B` lie in the local inverse's
source for all sufficiently close `B` in that cone. Its square is `B`, so the
local left-inverse identity gives `localInverse B = sqrt B`. Native eventual
equality transfers smoothness within the cone. This never asserts ambient
smoothness of the totalized `CFC.sqrt`.

Composition is native `ContDiffOn.comp`. The inverse version proves the square
root is a unit using `CFC.isUnit_sqrt_iff` and positive definiteness, then applies
`contDiffAt_ringInverse`. Empty rank needs no special branch: the kernel's
entrywise argument is vacuous, finite-dimensional equivalence still applies,
and all calculus and CFC instances support the singleton matrix algebra.

## Reproducibility and acceptance scope

Run `python scripts/verify-normalization-sqrt.py`. It checks pinned dependencies,
all 19 source declarations and their elaborated types, source stability, managed
build receipts, an allowed-only transitive axiom audit, and consumers including
the nonconstant polynomial family `(t²+1) • 1`, arbitrary subsets, empty rank,
inverse square roots, and the Sylvester inverse equation. The audit allows only
`propext`, `Classical.choice`, and `Quot.sound`.

Private publication and independent final review are recorded separately in
`verification/normalization-sqrt`. A successful bounded analytic proof does not
establish the parent normalization, gluing, or global manuscript theorem. No
GitHub upload or final project packaging is part of this delivery.
