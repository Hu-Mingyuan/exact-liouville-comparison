import ExactLiouvilleComparison.MoserExactnessCartan
import ExactLiouvilleComparison.MoserExactnessCancellation
import ExactLiouvilleComparison.MoserExactnessEndpointSteps
import ExactLiouvilleComparison.MoserExactnessIntegralRegularity

/-! Proved Moser pullback derivative and endpoint integral of spatial derivatives.
The smooth gauge and interchange of spatial differentiation with integration
are provided separately by the scalar integration theorem. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

theorem pullbackDerivative (mu : ℝ → M.Form 1) (hmu : M.IsSmoothFormFamily mu)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) (he : Equation mu Z)
    (E : FirstPathFlow.Evolution Z) : PullbackDerivative mu E :=
  pullbackDerivative_of_cartan mu E he (cartanTarget mu hmu Z hZ E)

/-- Integrability follows from the actual smooth contraction-family extension. -/
theorem derivativeIntegrand_integrable (mu : ℝ → M.Form 1)
    (hmu : M.IsSmoothFormFamily mu)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) (E : FirstPathFlow.Evolution Z)
    (x : M.Point) (v : M.Tangent x) :
    IntervalIntegrable (derivativeIntegrand mu E x v) MeasureTheory.volume 0 1 :=
  MoserExactnessIntegral.derivativeIntegrand_intervalIntegrable
    (contractionAlong_isSmoothIntervalScalarFamily mu hmu hZ E) x v

/-- Endpoint FTC with every regularity/integrability premise discharged. This is
not yet the identity with dH: the right side is the integral of spatial derivatives. -/
theorem endpoint_integral (mu : ℝ → M.Form 1) (hmu : M.IsSmoothFormFamily mu)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) (he : Equation mu Z)
    (E : FirstPathFlow.Evolution Z) (x : M.Point) (v : M.Tangent x) :
    evalOne (M.pullback M (E.map parameterZero parameterOne) (mu 1)) x v =
      evalOne (mu 0) x v + ∫ t in (0 : ℝ)..1, derivativeIntegrand mu E x v t :=
  endpoint_eq_integral_derivative mu E (pullbackDerivative mu hmu hZ he E) x v
    (derivativeIntegrand_integrable mu hmu hZ E x v)

end ExactLiouvilleComparison.MoserExactness
