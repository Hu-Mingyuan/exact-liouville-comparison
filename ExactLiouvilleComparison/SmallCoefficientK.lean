import ExactLiouvilleComparison.SmallCoefficient
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ExactLiouvilleComparison.SmallCoefficient
variable (G : AdmissibleGrowth 1)

def rate (rstar r : ℝ) : ℝ :=
  chi rstar r * (density G r / (2 * S G r) - 1 / r)

def k (rstar r : ℝ) : ℝ := Real.exp (∫ s in (1 : ℝ)..r, rate G rstar s)

/-- The endpoint-safe meaning of k prime throughout the closed half-line. -/
def kprime (rstar r : ℝ) : ℝ := derivWithin (k G rstar) (Ici 1) r

def m (rstar r : ℝ) : ℝ := k G rstar r + r * kprime G rstar r

theorem rate_smooth (rstar : ℝ) : ContDiffOn ℝ ∞ (rate G rstar) (Ici 1) := by
  apply (chi_smooth rstar).contDiffOn.mul
  apply ContDiffOn.sub
  · exact (density_smooth G).div (contDiffOn_const.mul (S_smooth G))
      (fun r hr => mul_ne_zero (by norm_num) (S_pos G hr).ne')
  · exact contDiffOn_const.div contDiffOn_id (fun r hr => ne_of_gt (by
      change 1 ≤ r at hr; linarith))

theorem rate_integrable (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    IntervalIntegrable (rate G rstar) volume 1 r :=
  ((rate_smooth G rstar).continuousOn.mono
    (by rw [uIcc_of_le hr]; exact Icc_subset_Ici_self)).intervalIntegrable

theorem k_smooth (rstar : ℝ) : ContDiffOn ℝ ∞ (k G rstar) (Ici 1) :=
  (contDiffOn_integral_Ici (rate_smooth G rstar)).exp

theorem k_hasDerivWithinAt (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    HasDerivWithinAt (k G rstar) (k G rstar r * rate G rstar r) (Ici 1) r := by
  exact
    (integral_hasDerivWithinAt_Ici (rate_smooth G rstar).continuousOn hr).exp

theorem kprime_eq (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    kprime G rstar r = k G rstar r * rate G rstar r :=
  (k_hasDerivWithinAt G rstar hr).derivWithin (uniqueDiffOn_Ici 1 r hr)

theorem k_hasDerivAt (rstar : ℝ) {r : ℝ} (hr : 1 < r) :
    HasDerivAt (k G rstar) (k G rstar r * rate G rstar r) r :=
  (k_hasDerivWithinAt G rstar hr.le).hasDerivAt (Ici_mem_nhds hr)

theorem kprime_eq_deriv (rstar : ℝ) {r : ℝ} (hr : 1 < r) :
    kprime G rstar r = deriv (k G rstar) r := by
  rw [kprime_eq G rstar hr.le, (k_hasDerivAt G rstar hr).deriv]

theorem k_pos (rstar r : ℝ) : 0 < k G rstar r := Real.exp_pos _

theorem rate_nonpos (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) : rate G rstar r ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (chi_nonneg rstar r)
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ (mul_pos (by norm_num) (S_pos G hr)) (by linarith : 0 < r)).2
  have hd := density_le_inv G hr
  have h := (le_div_iff₀ (by linarith : 0 < r)).1 hd
  have hs := one_le_S G hr
  nlinarith

theorem k_le_one (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) : k G rstar r ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := intervalIntegral.integral_mono_on hr (rate_integrable G rstar hr)
    (intervalIntegrable_const (c := (0 : ℝ))) (fun u hu => rate_nonpos G rstar hu.1)
  simpa using h

theorem k_eq_one {rstar r : ℝ} (hr : 1 ≤ r) (hrs : r ≤ rstar) : k G rstar r = 1 := by
  have h : (∫ u in (1 : ℝ)..r, rate G rstar u) = 0 := by
    calc
      _ = ∫ u in (1 : ℝ)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hr] at hu
        simp [rate, chi_zero (hu.2.trans hrs)]
      _ = 0 := by simp
  simp [k, h]

theorem kprime_nonpos (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) : kprime G rstar r ≤ 0 := by
  rw [kprime_eq G rstar hr]
  exact mul_nonpos_of_nonneg_of_nonpos (k_pos G rstar r).le (rate_nonpos G rstar hr)

theorem kprime_zero {rstar r : ℝ} (hr : 1 ≤ r) (hrs : r ≤ rstar) :
    kprime G rstar r = 0 := by
  simp [kprime_eq G rstar hr, rate, chi_zero hrs]

theorem m_eq (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    m G rstar r = k G rstar r *
      (1 - chi rstar r + chi rstar r * r ^ 2 / (2 * (G.B r) ^ 2 * S G r)) := by
  have hB := (G.positive r hr).ne'
  have hS := (S_pos G hr).ne'
  have hR : r ≠ 0 := ne_of_gt (by linarith)
  rw [m, kprime_eq G rstar hr]
  dsimp [rate, density]
  field_simp
  ring

theorem m_pos (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) : 0 < m G rstar r := by
  rw [m_eq G rstar hr]
  apply mul_pos (k_pos G rstar r)
  have hc := chi_nonneg rstar r
  have hc1 := chi_le_one rstar r
  have ht : 0 < r ^ 2 / (2 * (G.B r) ^ 2 * S G r) :=
    div_pos (sq_pos_of_pos (by linarith))
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (G.positive r hr))) (S_pos G hr))
  rw [mul_div_assoc]
  by_cases h : chi rstar r = 1
  · simpa [h] using ht
  · have hc' : chi rstar r < 1 := lt_of_le_of_ne hc1 h
    have hp := mul_nonneg hc ht.le
    linarith

end ExactLiouvilleComparison.SmallCoefficient
