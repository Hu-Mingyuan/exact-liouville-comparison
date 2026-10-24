import ExactLiouvilleComparison.ODETwoBarrierExistence
import ExactLiouvilleComparison.ODETwoBarrierSmooth

/-! Full native smooth evolution from the reviewed two one-sided barriers. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- The unchanged reviewed target. Compact confinement constructs finite trajectories;
localization and native uniqueness construct every field of the smooth evolution. -/
theorem twoBarrierEvolution : TwoBarrierEvolutionTarget (M := M) := by
  intro Z Ω hΩ hstrip hZ R hR hp hl Q hQ hcontrol C₀ C₁ hC₀ hC₁ hforward hpartial hreverse
  exact evolution_of_finite_existence Z hΩ hstrip hZ
    (twoBarrier_finiteIntervalExistence Z Ω hΩ hstrip hZ R hR hp hl Q hQ hcontrol
      C₀ C₁ hC₀ hC₁ hforward hpartial hreverse)

end ExactLiouvilleComparison.ODE
