import ExactLiouvilleComparison.MoserExactnessIntegral
import ExactLiouvilleComparison.MoserExactnessIntegralEuclideanChecks

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set MeasureTheory
namespace ExactLiouvilleComparison.MoserExactnessIntegral
variable {d : ℕ} {M : SmoothManifold d}

/-- Consumer in exactly the guarded native-derivative form required by endpoint FTC. -/
theorem ftc_integrability_consumer (f : Parameter → M.Point → ℝ)
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) (v : M.Tangent x) :
    IntervalIntegrable (fun t : ℝ => if ht : t ∈ parameterInterval then
      M.scalarDerivative (f ⟨t, ht⟩) x v else 0) volume 0 1 := by
  classical
  exact derivativeIntegrand_intervalIntegrable hf x v

/-- The original scalar integrand also meets endpoint continuity requirements. -/
theorem ftc_continuity_consumer (f : Parameter → M.Point → ℝ)
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) :
    ContinuousOn (fun t : ℝ => if ht : t ∈ parameterInterval then f ⟨t, ht⟩ x else 0)
      (Icc 0 1) := by
  classical
  exact integrand_continuousOn hf x

/-- The exported result uses the literal gauge, without an auxiliary extension. -/
theorem literal_integral_smooth (f : Parameter → M.Point → ℝ)
    (hf : M.IsSmoothIntervalScalarFamily f) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞
      (fun x => ∫ t in (0 : ℝ)..1,
        if ht : t ∈ parameterInterval then f ⟨t, ht⟩ x else 0) := by
  exact integral_smooth hf

/-- Literal guarded commutation at every actual native tangent vector. -/
theorem literal_scalarDerivative_integral (f : Parameter → M.Point → ℝ)
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun y => ∫ t in (0 : ℝ)..1,
      if ht : t ∈ parameterInterval then f ⟨t, ht⟩ y else 0) x v =
    ∫ t in (0 : ℝ)..1, if ht : t ∈ parameterInterval then
      M.scalarDerivative (f ⟨t, ht⟩) x v else 0 := by
  exact scalarDerivative_integral hf x v

end ExactLiouvilleComparison.MoserExactnessIntegral
