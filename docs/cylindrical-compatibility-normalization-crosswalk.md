# Supplied-metric normalization: pre-proof crosswalk

Mission `50754190-03fe-44b3-830e-5b109eca0470`, revision 1. This auxiliary
contract does not repeat or replace the reviewed cylindrical statement at
`24b8ee9589e80d6e415cf978e895cc33338deeb3`. It isolates normalization needed
for the compatible extension assertion following manuscript equation `eq:cylJ`.
The manuscript and all existing comparison assumptions remain unchanged.

## Native contract

`CylindricalCompatibilityNormalizationStatement.lean` imports Mathlib's native
`Geometry.Manifold.VectorBundle.Riemannian` and finite-dimensional normed-module
API. Its namespace is
`ExactLiouvilleComparison.CylindricalCompatibility.Normalization`.

| Mathematical input/output | Actual Lean meaning |
| --- | --- |
| Smooth real vector bundle | `FiberBundle F E`, `VectorBundle ℝ F E`, `ContMDiffVectorBundle ∞ F E IB` over `IsManifold IB ∞ B` |
| Finite rank, including zero | `FiniteDimensional ℝ F`; no `Nontrivial F` or positive dimension assumption |
| Two-form on fibers | `SymplecticForm.form x : E x →L[ℝ] E x →L[ℝ] ℝ`, continuous bilinear on the actual fibers |
| Alternating and nondegenerate | `form x v v = 0`; vanishing on all second arguments forces the first argument to vanish |
| Smoothness of the two-form | Native `ContMDiff` of its section into the iterated Hom bundle, with model fiber `F →L[ℝ] F →L[ℝ] ℝ` |
| Supplied metric | Native `Bundle.ContMDiffRiemannianMetric IB ∞ F E`, whose fields include the actual continuous bilinear metric, symmetry, strict positivity, bounded unit ball, and smooth section |
| Compatible endomorphism | Actual `J x : E x →L[ℝ] E x`, native smooth Hom-bundle section; square equals minus identity, form invariance, and positive `form x v (J x v)` for nonzero v |
| Recovery | At every x, for every compatible endomorphism J₀ of that one fiber, if `h.inner x v w = form x v (J₀ w)` for all v,w, then `J x = J₀` |

The input metric is explicit. Existing fiber norms give the topology for CLMs;
they are not silently identified with this supplied metric. There are no norm
estimates in this auxiliary contract. Any proof involving metric adjoints or
operator norms must install the metric-induced structure or prove its coordinate
formula. The eventual reference metric remains `g(v,w)=omega(v,Jw)` in the
parent's unchanged `CompatibleStructure`; it need not equal supplied h away
from recovery fibers.

No globally compatible J is an input. Recovery does not assume a global smooth
J₀, an extension, a square-root field, or a smoothness operation. Native Hom
bundles encode chart changes. The construction must either be intrinsic or
prove its local formulas agree under these changes before assembling the section.
No chartwise smoothness certificate is assumed. A local matrix proof will need
explicit conjugacy/naturality and transport lemmas.

`SymplecticForm` itself only needs the topological vector bundle and its section
smoothness predicate. Finite rank, smooth base and smooth bundle are explicit
binders on `NormalizationTarget`. Independent review detected and corrected
the omission of unused section variables from the elaborated target before proof work.

There is no exterior closedness hypothesis: this is a general vector-bundle
result, not a claim that an arbitrary base form is symplectic. For tangent-bundle
use, the parent's actual closed form supplies the input. General base manifolds
with corners are allowed; this does not add a boundary condition to the target
comparison theorem. No nonemptiness or connectedness of B is assumed. On an
empty base the output is the empty section; in rank zero the unique zero
endomorphism satisfies the square equation because every vector is zero and
strict positivity quantifies only nonzero vectors.

## Reuse and proof boundary

Mathlib `ContMDiffRiemannianMetric` is used directly rather than duplicating a
metric structure. `Hom.lean` provides native iterated Hom bundles and
`contMDiffAt_hom_bundle`; `Riemannian.lean` provides the metric's smoothness
meaning and conversion to `RiemannianBundle`. The small `SymplecticForm` record
adds only the necessary algebraic conditions to an actual native section.

The retained audit of FsFltz `CompatibleComplexPath` found two compatible
endpoints as inputs; it cannot provide existence. `CompatibleComplexExtension`
does not prove symplectic compatibility. The mandatory prior-cluster inspection
at `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c` found no CFC, polar, or
positive-definite normalization implementation; its `PrimitiveCutoffs.lean`
square-root occurrence is a scalar trigonometric identity. Neither source
supplies the missing analytic normalization.

Proposed formula, not yet a formal proof: define A by `h(Av,w)=omega(v,w)`;
then A is invertible and h-skew, and `J=A*(-A²)^(-1/2)` has the required positive
sign. Where `h=omega(.,J₀.)`, one has A=J₀ and `-A²=id`, giving recovery.
The smooth square-root and chart compatibility steps are obligations, not input
fields. `NormalizationTarget` is explicitly an unproved proposition. Its
successful compilation is only statement evidence. No normalization theorem,
final axiom audit, or mission acceptance is claimed by this file.
