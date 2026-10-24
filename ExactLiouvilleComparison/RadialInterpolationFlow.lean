import ExactLiouvilleComparison.RadialInterpolationFlowInputs
import ExactLiouvilleComparison.ODETwoBarrier

/-! Constructed radial interpolation Moser evolution on the full closed interval. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.RadialInterpolationFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- The unchanged reviewed manuscript bridge target, with no residual flow or
continuation premise. Forward R and reverse Q confinement supply the constructed
finite curves; native localization supplies the full smooth evolution. -/
theorem radialInterpolationFlow : Target (M := M) :=
  of_twoBarrier ODE.twoBarrierEvolution

/-- Choose the already proved evolution of the literal interpolation vector. -/
def evolution (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    FirstPathFlow.Evolution (MoserRegularity.interpolationField P q₀ q₁ σ hσ hw) :=
  Classical.choice (radialInterpolationFlow P q₀ q₁ horder htend σ hσ hw)

end ExactLiouvilleComparison.RadialInterpolationFlow
