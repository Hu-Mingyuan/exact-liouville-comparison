import ExactLiouvilleComparison.FirstPathFlowStatement

/-! Reusable finite-interval existence specification. This target remains unproved. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- The exact prerequisite: smoothness on one actual open neighborhood of the
closed spacetime strip, and a proper bounded-below scalar with a uniform actual
spatial derivative bound on the strip. No flow or continuation certificate is input. -/
def FiniteIntervalExistenceTarget : Prop :=
  ∀ (Z : ℝ → (x : M.Point) → M.Tangent x)
    (Ω : Set (ℝ × M.Point)), IsOpen Ω → parameterInterval ×ˢ univ ⊆ Ω →
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω →
    ∀ (P : M.Point → ℝ), ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P →
    IsProperMap P → BddBelow (range P) →
    ∀ D : ℝ, 0 ≤ D →
    (∀ t ∈ parameterInterval, ∀ x, |M.scalarDerivative P x (Z t x)| ≤ D) →
    ∀ (s : Parameter) (x : M.Point), ∃ γ : ℝ → M.Point,
      γ s.val = x ∧ ∀ t ∈ parameterInterval,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))
end ExactLiouvilleComparison.ODE
