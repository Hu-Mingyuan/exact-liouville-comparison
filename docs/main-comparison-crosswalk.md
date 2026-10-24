# General radial comparison: bounded definition crosswalk

Mission 92dedb29-ffc9-40f9-8d8c-07db9fc6ffbe, revision 1. The authoritative
`docs/reference/exact_liouville_comparison.tex` is unchanged. This specification
covers Theorem 1.1 and its four-path proof, not the application corollaries.
`MainComparison.Target` is definitionally the existing `MainTarget`; this file
and the statement module do not claim a proof.

## Exact source integration

Baseline f8b5b6bcb56a18c0094d15fed4619ff100327e30 is preserved byte for byte.
`verification/main-comparison/import-manifest.json` records all 203 file bindings
verified against the exact private deliveries: Moser/first path a7d1220ce86078b4c57df64447ce7743bd39a040,
third path c1773eba6457e4e3331cee126a6da07fc62333ac and algebra
7389b2f8b1b85a87eb83cb245cd3f3855c721dd5. The corresponding verified publications
are 1bdf8715-1cf6-454f-a5aa-05d9ede55a05, 014c546b-a118-4c3b-8e75-6a5af5d11848,
and 9898aa37-6d59-42dc-be16-41be6929e0c7. Existing algebra files matched their
delivered bytes. Moser source was read through the authenticated exact-commit
repository API because this checkout has protected Git metadata. Imported
receipts retain their original scope and source, not a claim about this assembly.

## Definitions and hypotheses

`SmoothManifold d` supplies a native finite-dimensional real smooth manifold
without boundary, with arbitrary natural dimension d. FsFltz `Tangent` is
Mathlib `TangentSpace`; `Form` is its native differential-form section;
`exteriorDerivative` uses `extDeriv`; `pullback` uses native `mfderiv`;
`SmoothEquiv` abbreviates Mathlib `Diffeomorph` at smoothness infinity.
No affine-space restriction is introduced.

`ExactSymplecticStructure` contains a smooth primitive and actual symplectic
exterior derivative. It carries no completeness assertion. `CompatibleStructure`
contains native smooth J, J²=-id, invariance and a native smooth Riemannian
metric g with g(v,w)=dβ(v,Jw). Its `MetricTangent`, `covector`, `dualNorm` and
`inverseContraction` explicitly transfer the same vector/covector to the g norm.
`inverseNorm` is the operator norm from the g-dual to the g tangent space,
constructed from nondegeneracy and finite dimension, with positive contraction
`dλ(Z,v)=λ(v)`. No chart norm or metric completeness substitutes for g.

`RadialReference` retains smooth proper R≥1, c>0, rstar>1, and precisely the
exterior identities β=-c dR∘J and c|dR|²_g≤R on R>rstar. `WeaklyTames` is
nonnegative dλ(v,Jv), separately from symplectic nondegeneracy. `AdmissibleGrowth 1`
quantifies arbitrary B, smooth on the closed ray, positive, B(r)≥r, with the
literal interval-integral primitive tending to infinity. `GrowthAtInfinity`
permits any compact exceptional K and positive C for the inverse-norm bound.
No restriction on λ, A, primitive completeness or completeness of g is added.
An object called a complete Liouville manifold continues to require the actual
FsFltz `CompleteLiouvilleFlow` for all real times; MainTarget does not use one.

## Four literal paths and bridge obligations

| Forward primitive | Existing actual evolution | Exactness application still to prove |
| --- | --- | --- |
| λ+t k(R)β | `FirstPathFlow.evolution` | Delivered `FirstPathExactness.firstPathExactness` and `exactComparison` discharge all premises |
| λ+((1-u)k(R)+u A(R))β | `MainComparison.secondEvolution` specializes `RadialInterpolationFlow.evolution` | Prove equality to affine form family, its time derivative and the literal field equation |
| A(R)β+sλ | `ThirdPath.evolution` | Reuse `primitive_family`, `primitive_parameter_derivative`, `field_intervalSmooth`, `field_equation` |
| (1+v(A(R)-1))β | `MainComparison.fourthEvolution` specializes `RadialInterpolationFlow.evolution` | Prove literal equality to sigma=0 interpolation and its derivative/field equation |

k is exactly `SmallCoefficient.k G P.rstar`. A is exactly `LargeCoefficient.A P
T.primitive`, constructed with proper compact sublevels. `second_applicable`
and `fourth_applicable` already discharge order, radial positivity, divergence,
and weak differential for the actual coefficients. The chosen evolutions are
constructed consequences, never new assumptions. `Evolution.map` takes initial
then final time. Its native ODE, open joint extension, uniqueness, inverse and
composition laws are outputs of proved existence. Smooth family and field
premises of `moserExactness` require actual open local extensions at the closed
interval endpoints; slice smoothness alone will not suffice.

`MoserExactness.Equation` is i_X dμ=-∂t μ, where the time derivative fixes x,v.
Its theorem supplies `Endpoint`: the literal H=∫₀¹ μ_t(X_t)(G_t(x)) dt is globally
smooth, G₁*μ₁=μ₀+dH, and G₁*dμ₁=dμ₀. The integral's extension outside [0,1]
is irrelevant to its value. `RemainingPathsTarget` demands these outputs for
the three named literal primitives and delivered evolutions, without free
flow, Cartan or integral regularity parameters.

## Endpoint direction, gauge and native conclusion

Write G1,...,G4 for the four forward endpoints, with gauges H1,...,H4.
Forward exactness compares μ1 to μ0. In `Witness.comp`, wF:source→middle and
wG:middle→target produce map F∘G (`G.trans F`) and gauge k+h∘G.
`Witness.symm` gives inverse map and gauge -h∘F⁻¹. Thus compose the inverse
fourth, inverse third, second, first witnesses to get
Ψ=G4⁻¹∘G3⁻¹∘G2∘G1 with Ψ*β=λ+df, then invert once:
F=Ψ⁻¹, h=-f∘F, F*λ=β+dh and F*dλ=dβ.
The final construction must expose these actual maps and gauges. The accepted
algebra constructs jointly smooth forward and inverse identity isotopies by
pointwise composition; this directly satisfies the unchanged native conclusion
without needing an additional concatenation assertion. Smooth isotopy has no
compact support requirement.

## Reuse inspection, in required order

1. Pinned Mathlib d13f23b: `Geometry/Manifold/Diffeomorph.lean`, `Diffeomorph.trans`,
   `coe_trans`, `symm`, and the native manifold derivative/form APIs. Search of
   Mathlib Geometry found no Moser exact comparison theorem replacing this
   application. Native affine derivative arithmetic is sufficient for the new
   scalar bridges (`HasDerivAt`, add/sub/const_mul, `deriv`).
2. Pinned FsFltz 1a3d387: `Geometry/Smooth.lean` definitions above and
   `Geometry/Liouville.lean` all-real `CompleteLiouvilleFlow`; existing project
   geometry uses these literally. No new geometric representation is needed.
3. Read-only prior cluster source under
   `/var/lib/archon-worker/imports/project-reference/archon_liouville` was searched
   for Moser/ExactComparison. No matching general radial theorem was found.
   Its complete-Liouville geometry cannot replace this general theorem.
4. Reuse the delivered exactness, flows, coefficients and algebra. New code is
   restricted to equality/time-derivative bridges, applications, and composition.

Independent statement review must cover the compiled module and these semantic
bytes before substantive proof work. Any change of target semantics requires
renewed review. MainTarget acceptance needs an actual proof and exact-source
final review, complete inventory, consumers and allowed-only transitive audit.
