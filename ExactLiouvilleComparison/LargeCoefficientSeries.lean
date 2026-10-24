import ExactLiouvilleComparison.SmallCoefficient
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The locally finite series in manuscript equation A, indexed by `j = n + 1`.
The geometric sequence is constructed separately; no growth bound is used here. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators

namespace ExactLiouvilleComparison.LargeCoefficient

def stepTerm (M : ℕ → ℝ) (rstar : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (M (n + 1) - M n) * SmallCoefficient.chi (rstar + n) r

def series (M : ℕ → ℝ) (rstar r : ℝ) : ℝ :=
  M 0 + ∑' n : ℕ, stepTerm M rstar n r

theorem stepTerm_zero (M : ℕ → ℝ) (rstar : ℝ) {n : ℕ} {r : ℝ}
    (hr : r ≤ rstar + n) : stepTerm M rstar n r = 0 := by
  simp [stepTerm, SmallCoefficient.chi_zero hr]

theorem series_eq_sum (M : ℕ → ℝ) (rstar : ℝ) {N : ℕ} {r : ℝ}
    (hr : r ≤ rstar + N) :
    series M rstar r = M 0 + ∑ n ∈ Finset.range N, stepTerm M rstar n r := by
  unfold series
  congr 1
  apply tsum_eq_sum
  intro n hn
  apply stepTerm_zero
  have hN : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
  have : (N : ℝ) ≤ n := by exact_mod_cast hN
  linarith

/-- A single finite range works on an open neighborhood of each real radius. -/
theorem series_locally_finite (M : ℕ → ℝ) (rstar r : ℝ) :
    ∃ N : ℕ, ∀ᶠ s in 𝓝 r, ∀ n, N ≤ n → stepTerm M rstar n s = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (r - rstar)
  refine ⟨N, ?_⟩
  filter_upwards [eventually_lt_nhds (show r < rstar + N by linarith)] with s hs
  intro n hn
  apply stepTerm_zero
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem stepTerm_smooth (M : ℕ → ℝ) (rstar : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (stepTerm M rstar n) :=
  contDiff_const.mul (SmallCoefficient.chi_smooth _)

theorem series_smooth (M : ℕ → ℝ) (rstar : ℝ) :
    ContDiff ℝ ∞ (series M rstar) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  obtain ⟨N, hN⟩ := exists_nat_gt (r - rstar)
  have heq : series M rstar =ᶠ[𝓝 r]
      (fun s => M 0 + ∑ n ∈ Finset.range N, stepTerm M rstar n s) := by
    filter_upwards [eventually_lt_nhds (show r < rstar + N by linarith)] with s hs
    exact series_eq_sum M rstar hs.le
  exact (contDiff_const.add (ContDiff.sum fun n _ => stepTerm_smooth M rstar n)).contDiffAt.congr_of_eventuallyEq heq

theorem series_eq_core (M : ℕ → ℝ) (rstar : ℝ) {r : ℝ} (hr : r ≤ rstar) :
    series M rstar r = M 0 := by
  simpa using series_eq_sum M rstar (N := 0) (by simpa using hr)

theorem stepTerm_nonneg {M : ℕ → ℝ} (hM : Monotone M) (rstar : ℝ) (n : ℕ) (r : ℝ) :
    0 ≤ stepTerm M rstar n r :=
  mul_nonneg (sub_nonneg.mpr (hM (Nat.le_succ n))) (SmallCoefficient.chi_nonneg _ _)

theorem series_ge_zero_term {M : ℕ → ℝ} (hM : Monotone M) (rstar r : ℝ) :
    M 0 ≤ series M rstar r := by
  unfold series
  exact le_add_of_nonneg_right (tsum_nonneg (fun n => stepTerm_nonneg hM rstar n r))

theorem series_monotone {M : ℕ → ℝ} (hM : Monotone M) (rstar : ℝ) :
    Monotone (series M rstar) := by
  intro r s hrs
  obtain ⟨N, hN⟩ := exists_nat_gt (s - rstar)
  have hs : s ≤ rstar + N := by linarith
  rw [series_eq_sum M rstar (hrs.trans hs), series_eq_sum M rstar hs]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left
  · exact Real.smoothTransition.monotone (sub_le_sub_right hrs _)
  · exact sub_nonneg.mpr (hM (Nat.le_succ n))

theorem series_deriv_nonneg {M : ℕ → ℝ} (hM : Monotone M) (rstar r : ℝ) :
    0 ≤ deriv (series M rstar) r :=
  (series_monotone hM rstar).deriv_nonneg

theorem series_radial_pos {M : ℕ → ℝ} (hM : Monotone M) (h0 : 1 ≤ M 0)
    (rstar : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    0 < series M rstar r + r * deriv (series M rstar) r := by
  have hA := series_ge_zero_term hM rstar r
  have hd := mul_nonneg (show 0 ≤ r by linarith) (series_deriv_nonneg hM rstar r)
  linarith

theorem series_ge_level {M : ℕ → ℝ} (hM : Monotone M) (rstar : ℝ)
    (n : ℕ) {r : ℝ} (hr : rstar + n ≤ r) : M n ≤ series M rstar r := by
  have heq : series M rstar (rstar + n) = M n := by
    rw [series_eq_sum M rstar le_rfl]
    have hsum : ∀ N : ℕ, M 0 + ∑ j ∈ Finset.range N, (M (j + 1) - M j) = M N := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ]; linarith
    rw [← hsum n]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
    rw [stepTerm, SmallCoefficient.chi_one (by linarith), mul_one]
  rw [← heq]
  exact series_monotone hM rstar hr

end ExactLiouvilleComparison.LargeCoefficient
