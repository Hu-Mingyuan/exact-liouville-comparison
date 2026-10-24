# Finite-interval native curve existence

Mission 0026c84b-1562-4164-9556-7e47f857440a, revision 1. Integration of the
first-path evolution remains owned by parent f03338c3-6a15-423a-a8bb-1990fa0a14df.

The unchanged, compiled, independently reviewed contract is
`ExactLiouvilleComparison.ODE.FiniteIntervalExistenceTarget` in
`ODEContinuationStatement.lean`. The theorem `ODE.finiteIntervalExistence`
inhabits that exact type. Verification status is recorded in
`verification/ode-continuation/receipt.json`; source code alone is not a build receipt.

## Proof

Fix the initial time s and point x. Properness and a lower bound for P make
K = {y | P(y) ≤ P(x) + D} compact. Construct a smooth spacetime cutoff χ,
valued in [0,1], equal to one near [0,1] × K, with compact support contained
in the supplied open smoothness domain Ω. The native section W(t,y) = χ(t,y) Z(t,y)
is globally smooth: the product tangent-bundle equivalence and the supported
section multiplication theorem prove the extension, including support-boundary
points. No regularity of Z outside Ω is required.

Pinned FsFltz `CollarFlow.exists_global_solution` constructs all-real native
solutions of W. Its proof suspends time with speed one, proves a uniform local
lifetime from compact spacetime support, applies native continuation, and proves
that the suspended time coordinate equals real time. It supplies an actual
`HasMFDerivAt` equation, not an assumed flow or continuation certificate.

On [0,1], linearity of the native differential and 0 ≤ χ ≤ 1 give
|dP(W)| ≤ D. The unchanged parent scalar displacement theorem therefore gives
|P(γ(t)) - P(x)| ≤ D |t-s| ≤ D, in either direction. Thus γ(t) lies in K,
χ(t,γ(t)) = 1, and the full native derivative equation of W is that of Z
at every t in [0,1], including both endpoints. No estimate outside the strip
is used. The all-real auxiliary curve is a total representative of the required
finite-interval curve; it is not claimed to solve Z outside [0,1].

## Scope

This delivery concerns only generic finite-interval existence.
Uniqueness for the original interval system, smooth dependence, evolution laws,
inverse diffeomorphisms, isotopy, first-path integration and full comparison
remain parent/root responsibilities. No metric or metric-completeness hypothesis
is needed: compactness is in the native manifold topology and the scalar bound
uses the actual differential. The reference metric and its norms remain exactly
as in the unchanged parent geometry inputs. No complete Liouville object is
introduced. No manuscript, dependency or accepted parent module is edited;
no PDF or GitHub publication belongs to this delivery.

## Reuse evidence

The pinned Mathlib local manifold ODE and uniform-time continuation interfaces
were inspected first. FsFltz `ProperExhaustionCompleteFlow` supplies autonomous
proper-exhaustion integration; it does not directly accept strip-local data.
`CollarFlow.timeSuspension`, `FamilyLiouvilleLocalFlow` and
`CollarSmoothEvolution` were inspected next. The decisive reusable producer is
`CollarEvolution.exists_global_solution`, imported by these interfaces.
`FamilyLiouvilleFieldExtension` demonstrates the native product-bundle bridge.
The old cluster `NativeCompleteFlow.lean` supremum/splicing construction at
commit 2c239b0c03922a1549f18ee3a45a8e0ca25bb28c was inspected read-only.
Its longer continuation construction is unnecessary here because the bounded
cutoff preserves the strip scalar estimate. This is a proof-route refinement,
not a change to the mission or any acceptance criterion.
