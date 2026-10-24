import ExactLiouvilleComparison.RadialInterpolationFlowStatement

/-! A separate analytic prerequisite. No trajectories or flows are assumed. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- A forward proper scalar and a uniformly coercive reverse barrier suffice.
The nonnegative partial time derivative makes the reverse estimate stable under
multiplication of the vector field by cutoffs valued in [0,1]. -/
def TwoBarrierEvolutionTarget : Prop :=
  ∀ (Z : ℝ → (x : M.Point) → M.Tangent x)
    (Ω : Set (ℝ × M.Point)), IsOpen Ω → parameterInterval ×ˢ univ ⊆ Ω →
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω →
    ∀ (R : M.Point → ℝ), ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ R →
    IsProperMap R → BddBelow (range R) →
    ∀ (Q : ℝ → M.Point → ℝ),
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => Q p.1 p.2) →
    (∀ L : ℝ, ∃ A : ℝ, ∀ t ∈ parameterInterval, ∀ x, Q t x ≤ L → R x ≤ A) →
    ∀ C₀ C₁ : ℝ, 0 ≤ C₀ → 0 ≤ C₁ →
    (∀ t ∈ parameterInterval, ∀ x, M.scalarDerivative R x (Z t x) ≤ C₀) →
    (∀ t ∈ parameterInterval, ∀ x, 0 ≤ deriv (fun u => Q u x) t) →
    (∀ t ∈ parameterInterval, ∀ x,
      -C₁ ≤ deriv (fun u => Q u x) t + M.scalarDerivative (Q t) x (Z t x)) →
    Nonempty (FirstPathFlow.Evolution (fun t : Parameter => Z t.val))
end ExactLiouvilleComparison.ODE
