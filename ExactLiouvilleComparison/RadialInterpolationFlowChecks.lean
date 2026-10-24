import ExactLiouvilleComparison.RadialInterpolationFlow
import ExactLiouvilleComparison.RadialInterpolationFlowCoefficients
import ExactLiouvilleComparison.RadialInterpolationFlowEqual

/-! Unconditional consumers of the constructed evolution, including manuscript paths two/four. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.RadialInterpolationFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- Actual literal-field trajectories through every initial point/time, including
both closed endpoints and either order of initial and terminal parameters. -/
theorem native_ode (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) (s : Parameter) (x : M.Point) :
    ∃ γ : ℝ → M.Point, γ s.val = x ∧ ContinuousOn γ parameterInterval ∧
      ∀ t : Parameter, HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ parameterInterval t.val
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (RadialInterpolation.vector (RadialInterpolation.coefficient q₀ q₁ t.val t.property)
            σ hσ hw (RadialInterpolation.delta q₀ q₁) (γ t.val))) := by
  let H := evolution P q₀ q₁ horder htend σ hσ hw
  refine ⟨fun t => H.extension s.val t x, ?_, (H.solves s x).1, ?_⟩
  · change H.extension s.val s.val x = x
    rw [H.agrees s s]
    exact H.initial s x
  · intro t
    exact (H.solves s x).2 t.val t.property t.property

/-- Degenerate differential d sigma=0 is permitted literally. -/
theorem sigma_zero (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop) :
    Nonempty (FirstPathFlow.Evolution (MoserRegularity.interpolationField P q₀ q₁
      0 M.isSmoothForm_zero RadialInterpolationChecks.weak_zero)) :=
  radialInterpolationFlow P q₀ q₁ horder htend 0 M.isSmoothForm_zero RadialInterpolationChecks.weak_zero

/-- Unit lower coefficient, arbitrary ordered upper coefficient, and weak sigma. -/
theorem unit_start (P : RadialReference M) (q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, 1 ≤ q₁.rho r)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    Nonempty (FirstPathFlow.Evolution (MoserRegularity.interpolationField P (oneCoefficient P) q₁ σ hσ hw)) := by
  apply radialInterpolationFlow P (oneCoefficient P) q₁ horder _ σ hσ hw
  change Tendsto (fun r : ℝ => r * 1) atTop atTop
  simp only [mul_one]
  exact tendsto_id

/-- Manuscript path two, using the delivered literal k and A without extra growth bounds. -/
theorem second_path (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    Nonempty (FirstPathFlow.Evolution (MoserRegularity.interpolationField P
      (FirstPath.coefficient P G) (largeCoefficient P T.primitive T.smooth_primitive)
      T.primitive T.smooth_primitive hw)) := by
  obtain ⟨ho, ht, _⟩ := second_applicable P G T hw
  exact radialInterpolationFlow P _ _ ho ht _ T.smooth_primitive hw

/-- Forward beta-to-A beta evolution; inverse endpoint gives the manuscript's fourth arrow. -/
theorem fourth_path (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) :
    Nonempty (FirstPathFlow.Evolution (MoserRegularity.interpolationField P
      (oneCoefficient P) (largeCoefficient P lam hlam)
      0 M.isSmoothForm_zero RadialInterpolationChecks.weak_zero)) := by
  obtain ⟨ho, ht, _⟩ := fourth_applicable P lam hlam
  exact radialInterpolationFlow P _ _ ho ht 0 M.isSmoothForm_zero RadialInterpolationChecks.weak_zero

/-- A vanishing field at a point fixes that point by closed-interval uniqueness. -/
theorem fixes_of_zero {Z : Parameter → (x : M.Point) → M.Tangent x}
    (H : FirstPathFlow.Evolution Z) (x : M.Point) (hz : ∀ u, Z u x = 0) (s t : Parameter) :
    H.map s t x = x := by
  symm
  apply H.unique s t (fun _ => x)
  refine ⟨continuousOn_const, ?_⟩
  intro u _ hu
  rw [hz ⟨u, hu⟩]
  simpa using (hasMFDerivWithinAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model d)) x
    (uIcc s.val t.val) u)

/-- The equal-coefficient evolution is the identity, without a divergence hypothesis. -/
theorem equal_identity (P : RadialReference M) (q : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    ∃ H : FirstPathFlow.Evolution (MoserRegularity.interpolationField P q q σ hσ hw),
      ∀ s t x, H.map s t x = x := by
  obtain ⟨H⟩ := equal_evolution P q σ hσ hw
  exact ⟨H, fun s t x => fixes_of_zero H x
    (fun u => RadialInterpolationChecks.equal_coefficients q u.val u.property σ hσ hw x) s t⟩

/-- The constructed general flow fixes every exterior critical point for all time pairs. -/
theorem critical_fixed (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) (x : M.Point)
    (hx : P.rstar < P.R x) (hdR : mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x = 0)
    (s t : Parameter) : (evolution P q₀ q₁ horder htend σ hσ hw).map s t x = x :=
  fixes_of_zero _ x (critical_field_zero P q₀ q₁ σ hσ hw x hx hdR) s t

/-- Actual inverse endpoint diffeomorphisms and identity-start isotopy, with no flow input. -/
theorem endpoint_inverse_isotopy (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    let H := evolution P q₀ q₁ horder htend σ hσ hw
    (H.map parameterZero parameterOne).symm = H.map parameterOne parameterZero ∧
    SmoothlyIsotopicToIdentity M (H.map parameterZero parameterOne) := by
  dsimp only
  exact ⟨(evolution P q₀ q₁ horder htend σ hσ hw).inverse _ _,
    (evolution P q₀ q₁ horder htend σ hσ hw).isotopy _⟩
end ExactLiouvilleComparison.RadialInterpolationFlow
