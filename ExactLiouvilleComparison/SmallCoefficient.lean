import ExactLiouvilleComparison.Statement
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Scalar primitives for manuscript equations S, k and m. No extension smoothness
is assumed: the auxiliary max extension is used only for the continuous FTC. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ExactLiouvilleComparison.SmallCoefficient

/-- FTC on a closed ray, including its lower endpoint. -/
theorem integral_hasDerivWithinAt_Ici {f : ℝ → ℝ} {a r : ℝ}
    (hf : ContinuousOn f (Ici a)) (hr : a ≤ r) :
    HasDerivWithinAt (fun x => ∫ u in a..x, f u) (f r) (Ici a) r := by
  let F : ℝ → ℝ := fun x => f (max a x)
  have hF : Continuous F := hf.comp_continuous (continuous_const.max continuous_id)
    (fun x => le_max_left a x)
  have heq : EqOn (fun x => ∫ u in a..x, f u) (fun x => ∫ u in a..x, F u) (Ici a) := by
    intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    simp only [F, max_eq_right hu.1]
  have hd := (hF.integral_hasStrictDerivAt a r).hasDerivAt.hasDerivWithinAt (s := Ici a)
  rw [show F r = f r by simp [F, max_eq_right hr]] at hd
  exact hd.congr heq (heq hr)

/-- A smooth integrand on a closed ray has a smooth primitive on that ray. -/
theorem contDiffOn_integral_Ici {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici a)) :
    ContDiffOn ℝ ∞ (fun x => ∫ u in a..x, f u) (Ici a) := by
  have hd := fun r hr => integral_hasDerivWithinAt_Ici hf.continuousOn (r := r) hr
  rw [contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ici a)]
  refine ⟨fun r hr => (hd r hr).differentiableWithinAt, hf.congr ?_⟩
  intro r hr
  exact (hd r hr).derivWithin (uniqueDiffOn_Ici a r hr)

variable (G : AdmissibleGrowth 1)

def density (r : ℝ) : ℝ := r / (G.B r) ^ 2

def S (r : ℝ) : ℝ := 1 + ∫ u in (1 : ℝ)..r, density G u

theorem density_smooth : ContDiffOn ℝ ∞ (density G) (Ici 1) :=
  contDiffOn_id.div (G.smooth.pow 2) (fun r hr => pow_ne_zero 2 (G.positive r hr).ne')

theorem density_pos {r : ℝ} (hr : 1 ≤ r) : 0 < density G r :=
  div_pos (by linarith) (sq_pos_of_pos (G.positive r hr))

theorem density_le_inv {r : ℝ} (hr : 1 ≤ r) : density G r ≤ 1 / r := by
  have hp : 0 < r := by linarith
  have hb := G.dominates r hr
  have hB := G.positive r hr
  apply (div_le_div_iff₀ (sq_pos_of_pos hB) hp).2
  nlinarith

theorem density_integrable {r : ℝ} (hr : 1 ≤ r) :
    IntervalIntegrable (density G) volume 1 r :=
  ((density_smooth G).continuousOn.mono (by rw [uIcc_of_le hr]; exact Icc_subset_Ici_self)).intervalIntegrable

theorem S_smooth : ContDiffOn ℝ ∞ (S G) (Ici 1) :=
  contDiffOn_const.add (contDiffOn_integral_Ici (density_smooth G))

theorem S_hasDerivWithinAt {r : ℝ} (hr : 1 ≤ r) :
    HasDerivWithinAt (S G) (density G r) (Ici 1) r := by
  change HasDerivWithinAt (fun x => 1 + ∫ u in (1 : ℝ)..x, density G u) _ _ _
  exact (integral_hasDerivWithinAt_Ici (density_smooth G).continuousOn hr).const_add 1

theorem S_derivWithin {r : ℝ} (hr : 1 ≤ r) :
    derivWithin (S G) (Ici 1) r = density G r :=
  (S_hasDerivWithinAt G hr).derivWithin (uniqueDiffOn_Ici 1 r hr)

theorem S_hasDerivAt {r : ℝ} (hr : 1 < r) : HasDerivAt (S G) (density G r) r :=
  (S_hasDerivWithinAt G hr.le).hasDerivAt (Ici_mem_nhds hr)

theorem one_le_S {r : ℝ} (hr : 1 ≤ r) : 1 ≤ S G r := by
  have h := intervalIntegral.integral_nonneg (μ := volume) hr (fun u hu => (density_pos G hu.1).le)
  dsimp [S]; linarith

theorem S_pos {r : ℝ} (hr : 1 ≤ r) : 0 < S G r := lt_of_lt_of_le zero_lt_one (one_le_S G hr)

theorem S_le_one_add_log {r : ℝ} (hr : 1 ≤ r) : S G r ≤ 1 + Real.log r := by
  have hi : IntervalIntegrable (fun u : ℝ => 1 / u) volume 1 r :=
    ((continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt (show 0 < u by
      rw [uIcc_of_le hr] at hu; linarith [hu.1])))).intervalIntegrable
  have h := intervalIntegral.integral_mono_on hr (density_integrable G hr) hi
    (fun u hu => density_le_inv G hu.1)
  rw [integral_one_div_of_pos zero_lt_one (show 0 < r by linarith), div_one] at h
  dsimp [S]; linarith

theorem S_tendsto : Tendsto (S G) atTop atTop := by
  exact tendsto_atTop_add_const_left _ _ G.divergent

theorem log_S_tendsto : Tendsto (fun r => Real.log (S G r)) atTop atTop :=
  Real.tendsto_log_atTop.comp (S_tendsto G)

/-- This is literally the manuscript theta(r-rstar). -/
def chi (rstar r : ℝ) : ℝ := Real.smoothTransition (r - rstar)

theorem chi_smooth (rstar : ℝ) : ContDiff ℝ ∞ (chi rstar) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem chi_nonneg (rstar r : ℝ) : 0 ≤ chi rstar r := Real.smoothTransition.nonneg _
theorem chi_le_one (rstar r : ℝ) : chi rstar r ≤ 1 := Real.smoothTransition.le_one _
theorem chi_zero {rstar r : ℝ} (hr : r ≤ rstar) : chi rstar r = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr)
theorem chi_one {rstar r : ℝ} (hr : rstar + 1 ≤ r) : chi rstar r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

end ExactLiouvilleComparison.SmallCoefficient
