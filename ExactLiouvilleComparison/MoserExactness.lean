import ExactLiouvilleComparison.MoserExactnessPullback
import ExactLiouvilleComparison.MoserExactnessIntegral
import ExactLiouvilleComparison.MoserExactnessExterior

/-! Cartan exactness with the literal globally smooth integral gauge. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

/-- Smoothness of the literal contraction integral, on the whole native manifold. -/
theorem gauge_smooth (mu : ℝ → M.Form 1) (hmu : M.IsSmoothFormFamily mu)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) (E : FirstPathFlow.Evolution Z) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (gauge mu E) :=
  MoserExactnessIntegral.integral_smooth
    (contractionAlong_isSmoothIntervalScalarFamily mu hmu hZ E)

/-- Native spatial differentiation commutes with the literal gauge integral. -/
theorem scalarDerivative_gauge (mu : ℝ → M.Form 1) (hmu : M.IsSmoothFormFamily mu)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) (E : FirstPathFlow.Evolution Z)
    (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (gauge mu E) x v =
      ∫ t in (0 : ℝ)..1, derivativeIntegrand mu E x v t :=
  MoserExactnessIntegral.scalarDerivative_integral
    (contractionAlong_isSmoothIntervalScalarFamily mu hmu hZ E) x v

/-- Manuscript eq:exactness for the actual identity-start evolution, with all
Cartan, gauge regularity, integral interchange and endpoint obligations proved. -/
theorem moserExactness : Target (M := M) := by
  intro mu hmu Z hZ he E
  have hs := gauge_smooth mu hmu hZ E
  have hp : ∀ x v, evalOne (M.pullback M (E.map parameterZero parameterOne) (mu 1)) x v =
      evalOne (mu 0) x v + M.scalarDerivative (gauge mu E) x v := by
    intro x v
    rw [scalarDerivative_gauge mu hmu hZ E x v]
    exact endpoint_integral mu hmu hZ he E x v
  refine ⟨pullbackDerivative mu hmu hZ he E, hs, hp, ?_⟩
  exact exterior_eq_of_primitive_eq (mu 0) (mu 1)
    (smoothForm_at mu hmu parameterZero) (smoothForm_at mu hmu parameterOne)
    (E.map parameterZero parameterOne) (gauge mu E) hs hp

end ExactLiouvilleComparison.MoserExactness
