import ExactLiouvilleComparison.MoserExactnessIntegralEuclidean

/-! Native smoothness and spatial differentiation of the literal interval integral. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set MeasureTheory
namespace ExactLiouvilleComparison.MoserExactnessIntegral
variable {d : ℕ} {M : SmoothManifold d}

/-- The literal guarded interval integral is globally smooth on the native manifold. -/
theorem integral_smooth {f : Parameter → M.Point → ℝ}
    (hf : M.IsSmoothIntervalScalarFamily f) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (integral f) := by
  obtain ⟨F, hF, heq⟩ := hf
  apply contMDiff_of_charts
  intro a
  rw [integral_comp_inverseChart heq]
  obtain ⟨U, hU, hsub, hG⟩ := hF a
  exact MoserExactnessIntegralEuclidean.contDiffOn_integral
    (chartAt (Model d) a).open_target hU hsub hG

set_option backward.isDefEq.respectTransparency false in
/-- Every actual tangent vector commutes with the literal guarded interval integral. -/
theorem scalarDerivative_integral {f : Parameter → M.Point → ℝ}
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (integral f) x v =
      ∫ t in (0 : ℝ)..1, derivativeIntegrand f x v t := by
  have hs := integral_smooth hf
  obtain ⟨F, hF, heq⟩ := hf
  rw [← M.fderiv_scalar_in_chart (integral f) hs x x (mem_chart_source _ _) v,
    integral_comp_inverseChart heq]
  obtain ⟨U, hU, hsub, hG⟩ := hF x
  have hD := MoserExactnessIntegralEuclidean.hasFDerivAt_integral hU hG
    (fun t ht => hsub ⟨ht, (chartAt (Model d) x).map_source (mem_chart_source _ _)⟩)
  exact (congrArg (fun L : Model d →L[ℝ] ℝ => L (M.chartTangentMap x x v))
    hD.fderiv).trans (derivativeIntegral_eq_chart hF heq x v).symm

/-- The full independently reviewed scalar integration contract. -/
theorem target : Target (M := M) := by
  intro f hf
  exact ⟨integral_smooth hf, integrand_continuousOn hf, integrand_intervalIntegrable hf,
    derivativeIntegrand_continuousOn hf, derivativeIntegrand_intervalIntegrable hf,
    scalarDerivative_integral hf⟩

end ExactLiouvilleComparison.MoserExactnessIntegral
