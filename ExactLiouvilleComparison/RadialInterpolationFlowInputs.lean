import ExactLiouvilleComparison.ODETwoBarrierStatement
import ExactLiouvilleComparison.ODEIntervalRegularity

/-! Proved native inputs for two-barrier continuation; no flow existence is claimed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.RadialInterpolationFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- Literal field identification, with no change of inverse contraction or sign. -/
theorem field_eq (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) (t : Parameter) (x : M.Point) :
    MoserRegularity.interpolationField P q₀ q₁ σ hσ hw t x =
      RadialInterpolation.vector (RadialInterpolation.coefficient q₀ q₁ t.val t.property)
        σ hσ hw (RadialInterpolation.delta q₀ q₁) x := rfl

/-- Smoothness is on all real time parameters, including spatial points with R=1. -/
theorem barrier_smooth (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => RadialInterpolation.Q q₀ q₁ p.1 (P.R p.2)) := by
  exact contDiff_mul.contMDiff.comp ((P.smooth_R.comp contMDiff_snd).prodMk_space
    ((contDiff_mul.contMDiff.comp ((contMDiff_const.sub contMDiff_fst).prodMk_space
      (q₀.smooth_comp.comp contMDiff_snd))).add
      (contDiff_mul.contMDiff.comp (contMDiff_fst.prodMk_space
        (q₁.smooth_comp.comp contMDiff_snd)))))

theorem barrier_time_derivative (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (t : ℝ) (x : M.Point) :
    deriv (fun u => RadialInterpolation.Q q₀ q₁ u (P.R x)) t =
      RadialInterpolation.delta q₀ q₁ (P.R x) * P.R x :=
  (RadialInterpolation.Q_parameter_derivative q₀ q₁ t (P.R x)).deriv

theorem barrier_time_nonneg (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r) (t : ℝ) (x : M.Point) :
    0 ≤ deriv (fun u => RadialInterpolation.Q q₀ q₁ u (P.R x)) t := by
  rw [barrier_time_derivative]
  exact mul_nonneg (sub_nonneg.mpr (horder _ (P.lower_R x)))
    (le_trans zero_le_one (P.lower_R x))

/-- One threshold works for every closed parameter; upper growth of q₁ is irrelevant. -/
theorem barrier_sublevel (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop) (L : ℝ) :
    ∃ A : ℝ, ∀ t ∈ parameterInterval, ∀ x,
      RadialInterpolation.Q q₀ q₁ t (P.R x) ≤ L → P.R x ≤ A := by
  obtain ⟨A, _, hA⟩ := RadialInterpolation.uniform_exhaustion q₀ q₁ horder htend (L+1)
  refine ⟨A, ?_⟩
  intro t ht x hx
  by_contra hn
  have hh := hA t ht (P.R x) (le_of_not_ge hn)
  linarith

/-- Explicit dependency adapter only. It proves applicability of every generic
hypothesis; the actual analytic theorem remains a separately owned prerequisite. -/
theorem of_twoBarrier (hflow : ODE.TwoBarrierEvolutionTarget (M := M)) : Target (M := M) := by
  intro P q₀ q₁ horder htend σ hσ hw
  obtain ⟨E, heq, Ω, hΩ, hstrip, hE⟩ := ODE.native_open_of_interval_family _
    (MoserRegularity.interpolation_intervalSmooth P q₀ q₁ σ hσ hw)
  obtain ⟨C₀, C₁, h₀, h₁, hb⟩ := MoserRegularity.interpolation_global P q₀ q₁ horder σ hσ hw
  have hr : ∀ t ∈ parameterInterval, ∀ x, M.scalarDerivative P.R x (E t x) ≤ C₀ := by
    intro t ht x
    simpa only [heq ⟨t, ht⟩] using (hb ⟨t, ht⟩ x).1
  have hQ : ∀ t ∈ parameterInterval, ∀ x,
      -C₁ ≤ deriv (fun u => RadialInterpolation.Q q₀ q₁ u (P.R x)) t +
        M.scalarDerivative (fun y => RadialInterpolation.Q q₀ q₁ t (P.R y)) x (E t x) := by
    intro t ht x
    rw [barrier_time_derivative]
    simpa only [MoserRegularity.barrierRate, heq ⟨t, ht⟩] using (hb ⟨t, ht⟩ x).2
  have hout := hflow E Ω hΩ hstrip hE P.R P.smooth_R P.proper_R
    ⟨1, by rintro _ ⟨x, rfl⟩; exact P.lower_R x⟩
    (fun t x => RadialInterpolation.Q q₀ q₁ t (P.R x)) (barrier_smooth P q₀ q₁)
    (barrier_sublevel P q₀ q₁ horder htend) C₀ C₁ h₀ h₁ hr
    (fun t _ x => barrier_time_nonneg P q₀ q₁ horder t x) hQ
  have hf : (fun t : Parameter => E t.val) =
      MoserRegularity.interpolationField P q₀ q₁ σ hσ hw := by
    funext t
    exact heq t
  rw [hf] at hout
  exact hout
end ExactLiouvilleComparison.RadialInterpolationFlow
