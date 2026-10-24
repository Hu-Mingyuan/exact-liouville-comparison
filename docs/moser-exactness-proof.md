# Moser exactness and the literal first-path gauge

This bounded library proves manuscript eq:exactness on the accepted arbitrary
native smooth manifolds. It also proves its unconditional application to the
constructed first-path evolution. Applications to the other three paths, the
full comparison and corollaries remain with the objective root.

## Public results

| Declaration | Proven result |
| --- | --- |
| `MoserExactness.cartanTarget` | Full time-dependent native Cartan pullback derivative, including within derivatives at both endpoints. |
| `MoserExactness.gauge_smooth` | Global native C∞ smoothness of the literal integral of μₜ(Xₜ)(Gₜ(x)). |
| `MoserExactness.scalarDerivative_gauge` | The actual native scalar derivative commutes with that interval integral. |
| `MoserExactness.moserExactness` | The unchanged generic `Target`: Moser pullback derivative, literal smooth gauge, G₁*μ₁=μ₀+dH, and G₁*dμ₁=dμ₀. |
| `FirstPathExactness.firstPathExactness` | The unchanged unconditional first-path `Target`, using λ+t k(R)β, the delivered field, and `FirstPathFlow.evolution`. |
| `FirstPathExactness.exactComparison` | `ExactComparison M (primitive P G T 1) T.primitive`, with the constructed endpoint, its isotopy, and the same integral gauge. |

All names above are under `ExactLiouvilleComparison`. The generic theorem takes
a genuine smooth form family, a genuine smooth interval vector-field family,
the signed native Moser equation, and an actual evolution. It proves Cartan
and integral calculus from those analytic data. The first-path theorem
constructs the evolution from the previously proved existence theorem and
discharges every smoothness and equation premise. Neither theorem assumes
exactness, integral differentiation, or the desired gauge identity.

## Definitions and endpoints

The statement gate and unchanged definition crosswalk are retained in
`docs/moser-exactness-crosswalk.md` and
`verification/moser-exactness/statement-review.md`. `SmoothManifold`, tangent
spaces, forms, `mfderiv`, exterior differentiation and pullback retain their
pinned meanings. Positive contraction places X in the first two-form slot:
dμₜ(Xₜ,v)=−∂ₜμₜ(v). Thus Cartan cancellation leaves the positive differential
of μₜ(Xₜ), giving the **plus** dH endpoint identity.

`gauge` is literally the interval integral from 0 to 1 of `contractionAlong`.
An `if` supplies zero outside the interval solely to represent an
interval-indexed field as an all-real integrand. No smoothness of this zero
extension across endpoints is asserted. Smoothness and derivative interchange
use the genuine locally defined open extensions and interval congruence.
No uniform exterior time strip on a noncompact manifold is required.

The first-path primitive is definitionally λ+t k(R)β with the delivered
`SmallCoefficient.k`. Its field is definitionally `FirstPath.X`. The generic
and first-path statements retain both endpoint derivatives and arbitrary
initial points. The actual first endpoint and its existing isotopy produce
the native `ExactComparison` conclusion.

## Proof route and reuse

1. The Cartan modules prove the Euclidean time-dependent pairing identity
   using the product/chain rules and symmetry of second derivatives. Native
   chart transport identifies spatial derivatives with `mfderiv` and time
   derivatives with the actual evolution ODE. `uniqueDiffOn_Icc_zero_one`
   handles both endpoint derivative identifications. No variational equation
   or Cartan identity is an input. The contraction-family extension is proved
   smooth by chart pairing and composition.
2. The integral Euclidean module uses Mathlib dominated differentiation under
   the integral. Compact-time/local-ball bounds, measurability and integrability
   are proved from smoothness on an open neighborhood. A finite-order induction,
   generalized over complete normed codomains and then applied to operator
   spaces, proves C∞ regularity. The native integral module transports this
   result through actual charts and proves the guarded scalar derivative
   formula. This meets the mandatory Mathlib, FsFltz, then prior cluster reuse
   order documented in the component crosswalks.
3. `pullbackDerivative_of_cartan` cancels the signed Moser terms.
   `endpoint_eq_integral_derivative` applies Mathlib endpoint FTC; its
   continuity and endpoint values follow from the derivative and actual
   evolution identity. `endpoint_integral` discharges integrability from
   the smooth contraction family. `scalarDerivative_gauge` turns the integral
   of spatial derivatives into dH.
4. `scalarForm` uses Mathlib constant zero-forms. Its exterior derivative is
   proved to evaluate as native `scalarDerivative`. Native naturality,
   additivity and d²=0 prove `exterior_eq_of_primitive_eq` and hence the
   two-form endpoint identity.
5. The six `FirstPathExactnessInputs` theorems prove primitive smoothness,
   joint smoothness, exterior-derivative and time-derivative identities, the
   actual field equation and joint field regularity. Their application to the
   previously constructed evolution proves `firstPathExactness` directly.

## Hypotheses and scope

The first-path result retains every admissible growth B, its C>0 and original
compact exception, weak taming and unrestricted primitive growth. The input
`P.compatible.inverseNorm` still uses the explicit metric g=dβ(·,J·), its
`MetricTangent` norm, dual norm and inverse-contraction operator norm. No chart
norm replaces these input norms; the generic calculus step needs no metric.
No metric completeness or primitive completeness hypothesis is added. These
are exact-symplectic results; nothing here identifies an incomplete evolution
with an all-real-time complete Liouville flow.

The statement, proof and axiom evidence for delegated components are preserved
in `verification/moser-exactness-cartan/`,
`verification/moser-exactness-integral/` and
`verification/moser-exactness-integral-euclidean/`. Parent integration checks
are reproduced by `python scripts/verify-moser-exactness-final.py`.
They cover both full targets, the native endpoint consumers, every declaration
in the owned Moser/first-path exactness namespaces (including generated/private
entries), their fully elaborated types and transitive axiom closure. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted.

This contribution remains private. It changes no authoritative manuscript,
accepted semantic module, dependency pin, ThirdPath or ExactComparisonAlgebra
worker file, and creates no final PDF or GitHub publication.
