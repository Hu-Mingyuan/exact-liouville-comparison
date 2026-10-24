import ExactLiouvilleComparison.MoserExactnessStatement

/-! Endpoint FTC reduction. The analytic integrability premise is discharged by
smooth interval integration in the final consumer, not added to its target. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

def derivativeIntegrand (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) (x : M.Point) (v : M.Tangent x) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ parameterInterval then
    M.scalarDerivative (contractionAlong mu E ⟨t, ht⟩) x v else 0

/-- The endpoint fundamental theorem of calculus for the actual pullback.
This result proves only the integral of spatial derivatives identity; exchanging
that derivative and the integral is a separate analytic theorem. -/
theorem endpoint_eq_integral_derivative (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) (hd : PullbackDerivative mu E)
    (x : M.Point) (v : M.Tangent x)
    (hi : IntervalIntegrable (derivativeIntegrand mu E x v) MeasureTheory.volume 0 1) :
    evalOne (M.pullback M (E.map parameterZero parameterOne) (mu 1)) x v =
      evalOne (mu 0) x v + ∫ t in (0 : ℝ)..1, derivativeIntegrand mu E x v t := by
  classical
  let f := fun t => evalOne (M.pullback M (E.extension 0 t) (mu t)) x v
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hd ⟨t, ht⟩ x v).continuousWithinAt
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt f (derivativeIntegrand mu E x v t) t := by
    intro t ht
    have htI : t ∈ parameterInterval := ⟨ht.1.le, ht.2.le⟩
    simpa only [derivativeIntegrand, dite_eq_left htI, f] using
      (hd ⟨t, htI⟩ x v).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hcont hder hi
  have h0map : E.extension 0 0 = id := by
    rw [show (0 : ℝ) = parameterZero.val from rfl, E.agrees]
    funext y
    exact E.initial parameterZero y
  have h0 : f 0 = evalOne (mu 0) x v := by
    dsimp only [f]
    rw [h0map, M.pullback_id]
  have h1 : f 1 = evalOne (M.pullback M (E.map parameterZero parameterOne) (mu 1)) x v := by
    dsimp only [f]
    rw [show (0 : ℝ) = parameterZero.val from rfl,
      show (1 : ℝ) = parameterOne.val from rfl, E.agrees]
  rw [h0, h1] at hFTC
  linarith

end ExactLiouvilleComparison.MoserExactness
