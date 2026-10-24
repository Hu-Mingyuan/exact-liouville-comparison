import ExactLiouvilleComparison.RadialInterpolationFlowInputs
import ExactLiouvilleComparison.FirstPathFlow

/-! Equal-coefficient case: a genuinely constructed evolution without a divergence hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.RadialInterpolationFlow
variable {d : ℕ} {M : SmoothManifold d}

theorem equal_evolution (P : RadialReference M) (q : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    Nonempty (FirstPathFlow.Evolution (MoserRegularity.interpolationField P q q σ hσ hw)) := by
  obtain ⟨E, heq, Ω, hΩ, hstrip, hE⟩ := ODE.native_open_of_interval_family _
    (MoserRegularity.interpolation_intervalSmooth P q q σ hσ hw)
  have hz (t : Parameter) (x : M.Point) : E t.val x = 0 := by
    rw [heq t]
    exact RadialInterpolationChecks.equal_coefficients q t.val t.property σ hσ hw x
  have hb : ∀ t ∈ parameterInterval, ∀ x, |M.scalarDerivative P.R x (E t x)| ≤ 0 := by
    intro t ht x
    rw [hz ⟨t, ht⟩ x]
    simp [scalarDerivative]
  have hout := FirstPathFlow.evolution_of_scalar_bound E hΩ hstrip hE P.R
    P.smooth_R P.proper_R ⟨1, by rintro _ ⟨x, rfl⟩; exact P.lower_R x⟩ (le_refl 0) hb
  have hf : (fun t : Parameter => E t.val) =
      MoserRegularity.interpolationField P q q σ hσ hw := by
    funext t
    exact heq t
  rw [hf] at hout
  exact hout

/-- An exterior critical point is a stationary point for every parameter, including endpoints. -/
theorem critical_field_zero (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) (x : M.Point)
    (hx : P.rstar < P.R x)
    (hdR : mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x = 0) (t : Parameter) :
    MoserRegularity.interpolationField P q₀ q₁ σ hσ hw t x = 0 :=
  RadialInterpolationChecks.critical_point _ σ hσ hw _ x hx hdR
end ExactLiouvilleComparison.RadialInterpolationFlow
