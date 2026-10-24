# Normalization algebra proof route

The steps below are implemented and compile against the pinned dependencies.
The auxiliary statement and all three target propositions are unchanged from
the independent pre-proof review. Final acceptance additionally requires the
source-bound audit and independent final review recorded in the dedicated
verification directory.

Write H=sqrt(G), B=H inverse, K=-B W B, Q=sqrt(-(K*K)), L=K Q inverse.
The construction is J=B L H. The identities below are proved from
G.PosDef, W.transpose=-W and IsUnit W, without additional certificates.

1. Native matrix/form bridges establish alternation, nondegeneracy and
   congruence evaluation. H and B are symmetric positive definite, H H=G.
2. K is skew and invertible, so -(K K)=K.transpose K is positive definite.
   Actual CFC positivity, invertibility and square identities give Q. CFC
   commutation gives K Q=Q K, hence K Q inverse=Q inverse K.
3. L L=-1 and -K L=Q. Thus J J=-1 and W J=H Q H is positive definite.
   Symmetry of W J gives J.transpose W=-W J; multiply by J to obtain
   J.transpose W J=W. Native positive quadratic evaluation proves the
   strict compatibility inequality.
4. Recovery uses only G=W J0 and J0 J0=-1: W=-G J0, K=H J0 B, K K=-1,
   Q=1, so J=J0.
5. Given arbitrary invertible P, put G'=P.transpose G P, W'=P.transpose W P,
   H'=sqrt(G'), B'=H' inverse, U=H P B'. Prove U.transpose U=1 and
   U U.transpose=1. Then K'=U.transpose K U. The positive matrix
   U.transpose Q U squares to -(K' K'); CFC.sqrt_unique proves Q' equals
   it. Transport inverses and obtain L'=U.transpose L U. Finally use
   U H'=H P and B' U.transpose=P inverse B to prove the stated naturality.

No Nonempty assumption is needed. Matrix inverse and CFC arguments continue
on the trivial zero-rank matrix algebra; any library API requiring Nontrivial
must be avoided or treated by an explicit zero-rank branch.


## Public integration interface

Import `ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraNative`
for the matrix theorems and native coordinate consumers. All names are in
`ExactLiouvilleComparison.NormalizationAlgebra`.

| Declaration | Result |
| --- | --- |
| `normalize` | Literal total CFC/inverse formula in the unchanged statement module |
| `normalize_compatible` | Compatibility for `G.PosDef`, `W.transpose=-W`, `IsUnit W` |
| `normalize_metric` | `W * normalize G W = metricRoot G * polarRoot G W * metricRoot G` |
| `normalize_recovery` | Equality to `J` assuming only `G.PosDef`, `J*J=-1`, `G=W*J` |
| `normalize_naturality` | `normalize (pull P G) (pull P W) = P⁻¹ * normalize G W * P` for every invertible `P` |
| `normalizationContract`, `recoveryContract`, `naturalityContract` | Actual proofs of the three reviewed targets |
| `form_isAlt`, `form_nondegenerate_iff`, `form_pull` | Native bilinear-form bridges |
| `associated_operator_equation`, `skew_eq_whitened_operator` | Sign and whitening bridges for `g(Av,w)=omega(v,w)` |
| `endomorphism`, `continuousForm` | Native continuous linear and bilinear maps with literal evaluation bridges |
| `normalize_native`, `normalize_native_naturality` | Compatibility and naturality evaluated through the native maps |
| `normalize_rank_zero` | The unique zero-rank endomorphism is retained |

The `Checks` module adds a canonical-plane recovery example fixing the sign,
a native recovery consumer, and proofs that all zero-rank matrices meet the
admissibility conditions and yield compatibility. No assumption of positive
rank, even rank, orientation-preserving coordinates, or an already compatible
structure is used in the general construction.

The matrix CFC is the pinned native real-matrix CFC. Its use does not assert a
CFC instance for arbitrary real Hilbert-space endomorphisms. Arbitrary `P` is
never passed off as a star equivalence. `whitening_orthogonal` proves the exact
orthogonality needed by `sqrt_pull_orthogonal`, which in turn uses actual
`CFC.sqrt_unique` and positive-semidefinite congruence.

The local helpers `polar_factor_sq` and `polar_factor_metric` take algebraic
identities as premises; these are internal lemmas. The public construction
always discharges those premises with `polarRoot_sq`, `polarRoot_posDef`, and
`polarRoot_commute`, proved from the original metric/form assumptions. They are
not assumed square-root or normalization certificates.

No norm estimate is claimed. The metric remains exactly `form G`; native
coordinate CLMs use the existing coordinate topology only to express continuity.
Smooth dependence and assembly on the tangent bundle remain with the analytic
sibling and parent normalization owner. The full cylindrical extension and
Liouville comparison are not proved by this algebraic prerequisite alone.

## Reproduction

Run `python scripts/verify-normalization-algebra.py`. It serially runs managed
module/consumer compilation, complete declaration-type inventory, and transitive
axiom collection. It checks source stability, equal managed source fingerprints,
exact dependency pins, the unchanged reviewed statement and manuscript hashes,
and the allowed set `{propext, Classical.choice, Quot.sound}` for every collected
declaration. It writes `verification/normalization-algebra/receipt.json`,
`types.txt`, and `axioms.tsv`. The independent reviews and exact private-source
publication binding are retained in the same directory. No upstream files or
shared geometry/statement modules are changed by this mission.
