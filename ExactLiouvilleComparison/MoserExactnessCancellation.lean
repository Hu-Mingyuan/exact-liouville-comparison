import ExactLiouvilleComparison.MoserExactnessStatement

/-! Algebraic cancellation in Cartan once the analytic identity is established.
This is not an assumption in, or proof of, the full exactness target. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

theorem pullbackDerivative_of_cartan (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) (he : Equation mu Z)
    (hc : CartanDerivative mu E) : PullbackDerivative mu E := by
  intro t x v
  have h := hc t x v
  dsimp only at h
  rw [he, add_neg_cancel, zero_add] at h
  exact h

end ExactLiouvilleComparison.MoserExactness
