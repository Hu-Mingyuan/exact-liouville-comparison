import ExactLiouvilleComparison.MoserRegularityCompact

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserRegularity
variable {d : ℕ} {M : SmoothManifold d}

/-- The original arbitrary compact growth exception is retained when globalizing. -/
theorem first_global (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Parameter, ∀ x,
      |M.scalarDerivative (FirstPath.exhaustion P G) x (firstField P G T hw t x)| ≤ D := by
  classical
  obtain ⟨L, hL, _, htail⟩ := FirstPath.exterior_estimate P G T hw hC K hK hb
  obtain ⟨D, hD, hcore⟩ := (first_compact P G T hw).2 L hL
  refine ⟨max D (Real.sqrt 2 * C * SmallCoefficient.b0 G P.rstar),
    hD.trans (le_max_left _ _), ?_⟩
  intro t x
  by_cases hx : x ∈ L
  · exact (hcore t x hx).trans (le_max_left _ _)
  · exact (htail x hx t.val t.property.1).trans (le_max_right _ _)

/-- A generic consumer of unchanged GrowthAtInfinity, without global strengthening. -/
theorem first_growth_consumer (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (hg : GrowthAtInfinity P.compatible T P.R 1) :
    ∃ G : AdmissibleGrowth 1, NativeJoint (firstField P G T hw) ∧
      IsProperMap (FirstPath.exhaustion P G) ∧
      BddBelow (range (FirstPath.exhaustion P G)) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Parameter, ∀ x,
        |M.scalarDerivative (FirstPath.exhaustion P G) x (firstField P G T hw t x)| ≤ D := by
  obtain ⟨G, C, hC, K, hK, hb⟩ := hg
  exact ⟨G, first_joint P G T hw, FirstPath.exhaustion_proper P G,
    FirstPath.exhaustion_bddBelow P G, first_global P G T hw hC K hK hb⟩

/-- Native spatial derivative of the barrier, including R=1. -/
theorem Q_scalarDerivative (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (t : Parameter) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun y => RadialInterpolation.Q q₀ q₁ t.val (P.R y)) x v =
      ((RadialInterpolation.coefficient q₀ q₁ t.val t.property).rho (P.R x) + P.R x *
        (RadialInterpolation.coefficient q₀ q₁ t.val t.property).rhoPrime (P.R x)) *
      M.scalarDerivative P.R x v := by
  have h := (RadialInterpolation.Q_radial_derivative q₀ q₁ t.val (P.lower_R x)).hasFDerivWithinAt.hasMFDerivWithinAt.comp x
      (P.smooth_R.mdifferentiable (by simp) x).hasMFDerivAt.hasMFDerivWithinAt
      (fun y (_ : y ∈ (univ : Set M.Point)) => P.lower_R y)
  have he := h.mfderivWithin (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ, Model d)))
  rw [mfderivWithin_univ] at he
  unfold scalarDerivative
  rw [show (fun y => RadialInterpolation.Q q₀ q₁ t.val (P.R y)) =
      (RadialInterpolation.Q q₀ q₁ t.val) ∘ P.R from rfl, he]
  rw [RadialInterpolation.coefficient_prime q₀ q₁ t.val t.property (P.lower_R x)]
  change M.scalarDerivative P.R x v * _ = _
  change _ = (RadialInterpolation.rho q₀ q₁ t.val (P.R x) + P.R x * _) * _
  dsimp only [scalarDerivative]
  ring

theorem barrierRate_eq (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (Z : Parameter → (x : M.Point) → M.Tangent x) (t : Parameter) (x : M.Point) :
    barrierRate P q₀ q₁ Z t x =
      RadialInterpolation.delta q₀ q₁ (P.R x) * P.R x +
      ((RadialInterpolation.coefficient q₀ q₁ t.val t.property).rho (P.R x) + P.R x *
        (RadialInterpolation.coefficient q₀ q₁ t.val t.property).rhoPrime (P.R x)) *
      M.scalarDerivative P.R x (Z t x) := by
  rw [barrierRate, Q_scalarDerivative]

/-- Global upper radial and lower barrier bounds, without trajectories. -/
theorem interpolation_global (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ t : Parameter, ∀ x,
      M.scalarDerivative P.R x (interpolationField P q₀ q₁ σ hσ hw t x) ≤ C₀ ∧
      -C₁ ≤ barrierRate P q₀ q₁ (interpolationField P q₀ q₁ σ hσ hw) t x := by
  obtain ⟨_, C₀, C₁, h₀, h₁, hcore⟩ := interpolation_compact P q₀ q₁ σ hσ hw
  refine ⟨C₀, C₁, h₀, h₁, ?_⟩
  intro t x
  by_cases hx : P.R x ≤ P.rstar
  · exact hcore t x hx
  · have hx' := lt_of_not_ge hx
    have hr := (RadialInterpolation.radial (RadialInterpolation.coefficient q₀ q₁ t.val t.property)
      σ hσ hw (RadialInterpolation.delta q₀ q₁) x hx'
      (sub_nonneg.mpr (horder _ (P.lower_R x)))).1
    have hQ := RadialInterpolation.Q_directional q₀ q₁ horder t.val t.property σ hσ hw x hx'
    constructor
    · change 0 ≤ -M.scalarDerivative P.R x (interpolationField P q₀ q₁ σ hσ hw t x) at hr
      linarith
    · rw [barrierRate_eq]
      exact (neg_nonpos.mpr h₁).trans (hQ.2.trans hQ.1)

end ExactLiouvilleComparison.MoserRegularity
