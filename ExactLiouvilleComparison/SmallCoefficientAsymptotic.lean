import ExactLiouvilleComparison.SmallCoefficientK
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ExactLiouvilleComparison.SmallCoefficient
variable (G : AdmissibleGrowth 1)

theorem k_antitone (rstar : ℝ) : AntitoneOn (k G rstar) (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1) (k_smooth G rstar).continuousOn
  · intro r hr
    rw [interior_Ici, mem_Ioi] at hr
    exact (k_hasDerivAt G rstar hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ici, mem_Ioi] at hr
    rw [← kprime_eq_deriv G rstar hr]
    exact kprime_nonpos G rstar hr.le

def logProfile (r : ℝ) : ℝ := Real.log (S G r) / 2 - Real.log r

theorem logProfile_hasDerivAt {r : ℝ} (hr : 1 < r) :
    HasDerivAt (logProfile G) (density G r / (2 * S G r) - 1 / r) r := by
  have hd := ((S_hasDerivAt G hr).log (S_pos G hr.le).ne').div_const 2
  have he := hd.sub (Real.hasDerivAt_log (ne_of_gt (show 0 < r by linarith)))
  convert he using 1 <;> first | rfl | ring

theorem rate_integral_tail {rstar r : ℝ} (hs : 1 < rstar) (hr : rstar + 1 ≤ r) :
    (∫ u in rstar + 1..r, rate G rstar u) = logProfile G r - logProfile G (rstar + 1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [uIcc_of_le hr] at hu
    have hu1 : 1 < u := by linarith [hu.1]
    simpa only [rate, chi_one hu.1, one_mul] using logProfile_hasDerivAt G hu1
  · exact ((rate_smooth G rstar).continuousOn.mono (by
      rw [uIcc_of_le hr]
      intro u hu
      show 1 ≤ u
      linarith [hu.1])).intervalIntegrable

/-- The actual positive integration constant, independent of the large radius. -/
def b0 (rstar : ℝ) : ℝ :=
  Real.exp ((∫ u in (1 : ℝ)..rstar + 1, rate G rstar u) - logProfile G (rstar + 1))

theorem b0_pos (rstar : ℝ) : 0 < b0 G rstar := Real.exp_pos _

theorem exp_logProfile {r : ℝ} (hr : 1 ≤ r) :
    Real.exp (logProfile G r) = Real.sqrt (S G r) / r := by
  rw [logProfile, Real.exp_sub, Real.exp_half, Real.exp_log (S_pos G hr),
    Real.exp_log (show 0 < r by linarith)]

theorem k_tail {rstar r : ℝ} (hs : 1 < rstar) (hr : rstar + 1 ≤ r) :
    k G rstar r = b0 G rstar * Real.sqrt (S G r) / r := by
  have ht : 1 ≤ rstar + 1 := by linarith
  have hi := intervalIntegral.integral_add_adjacent_intervals (rate_integrable G rstar ht)
    (((rate_smooth G rstar).continuousOn.mono (by
      rw [uIcc_of_le hr]
      intro u hu
      exact ht.trans hu.1)).intervalIntegrable)
  rw [rate_integral_tail G hs hr] at hi
  unfold k
  rw [← hi]
  have ha : (∫ u in (1 : ℝ)..rstar + 1, rate G rstar u) +
      (logProfile G r - logProfile G (rstar + 1)) =
      ((∫ u in (1 : ℝ)..rstar + 1, rate G rstar u) - logProfile G (rstar + 1)) +
      logProfile G r := by ring
  rw [ha, Real.exp_add, exp_logProfile G (ht.trans hr)]
  dsimp [b0]
  ring

theorem m_tail {rstar r : ℝ} (hs : 1 < rstar) (hr : rstar + 1 ≤ r) :
    m G rstar r = b0 G rstar * r / (2 * (G.B r) ^ 2 * Real.sqrt (S G r)) := by
  have hr1 : 1 ≤ r := by linarith
  have hB := (G.positive r hr1).ne'
  have hS := (S_pos G hr1).ne'
  have hR : r ≠ 0 := ne_of_gt (by linarith)
  have hq := (Real.sqrt_pos.mpr (S_pos G hr1)).ne'
  have hsq := Real.sq_sqrt (S_pos G hr1).le
  rw [m_eq G rstar hr1, chi_one hr, k_tail G hs hr]
  simp only [sub_self, zero_add, one_mul]
  field_simp
  rw [hsq]

theorem exists_tail_constant {rstar : ℝ} (hs : 1 < rstar) :
    ∃ b : ℝ, 0 < b ∧ ∀ r, rstar + 1 ≤ r →
      k G rstar r = b * Real.sqrt (S G r) / r ∧
      m G rstar r = b * r / (2 * (G.B r) ^ 2 * Real.sqrt (S G r)) :=
  ⟨b0 G rstar, b0_pos G rstar, fun _ hr => ⟨k_tail G hs hr, m_tail G hs hr⟩⟩

theorem radius_mul_k_tendsto {rstar : ℝ} (hs : 1 < rstar) :
    Tendsto (fun r => r * k G rstar r) atTop atTop := by
  have h := (Real.tendsto_sqrt_atTop.comp (S_tendsto G)).const_mul_atTop (b0_pos G rstar)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (rstar + 1)] with r hr
  rw [k_tail G hs hr]
  have hR : r ≠ 0 := ne_of_gt (by linarith)
  field_simp
  rfl

end ExactLiouvilleComparison.SmallCoefficient

namespace ExactLiouvilleComparison.SmallCoefficient
variable (G : AdmissibleGrowth 1)

theorem S_one : S G 1 = 1 := by simp [S]

theorem S_monotone : MonotoneOn (S G) (Set.Ici 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 1) (S_smooth G).continuousOn
  · intro r hr
    rw [interior_Ici, mem_Ioi] at hr
    exact (S_hasDerivAt G hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ici, mem_Ioi] at hr
    rw [(S_hasDerivAt G hr).deriv]
    exact (density_pos G hr.le).le

theorem log_S_hasDerivWithinAt {r : ℝ} (hr : 1 ≤ r) :
    HasDerivWithinAt (fun x => Real.log (S G x))
      (density G r / S G r) (Ici 1) r :=
  (S_hasDerivWithinAt G hr).log (S_pos G hr).ne'

/-- The actual exponential-integral formula with the endpoint-correct S prime. -/
theorem k_formula (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    k G rstar r = Real.exp (∫ u in (1 : ℝ)..r,
      chi rstar u * (derivWithin (S G) (Ici 1) u / (2 * S G u) - 1 / u)) := by
  unfold k
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hr] at hu
  change rate G rstar u = chi rstar u *
    (derivWithin (S G) (Ici 1) u / (2 * S G u) - 1 / u)
  rw [S_derivWithin G hu.1]
  rfl

theorem kprime_smooth (rstar : ℝ) : ContDiffOn ℝ ∞ (kprime G rstar) (Ici 1) := by
  apply ((k_smooth G rstar).mul (rate_smooth G rstar)).congr
  intro r hr
  exact kprime_eq G rstar hr

theorem m_smooth (rstar : ℝ) : ContDiffOn ℝ ∞ (m G rstar) (Ici 1) :=
  (k_smooth G rstar).add (contDiffOn_id.mul (kprime_smooth G rstar))

end ExactLiouvilleComparison.SmallCoefficient
