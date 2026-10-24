import ExactLiouvilleComparison.SteinGrowthStatement
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A bounded modification of an admissible function, preserving its literal
interval-integral divergence. No geometric comparison theorem is used. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter MeasureTheory

namespace ExactLiouvilleComparison.SteinGrowth

/-- The cutoff vanishes on a neighborhood of the old left endpoint. -/
def extendedFunction (B : AdmissibleGrowth (Real.exp 1)) (r : ℝ) : ℝ :=
  r + Real.smoothTransition (r - (Real.exp 1 + 1)) * (B.B r - r)

theorem extendedFunction_eq_id (B : AdmissibleGrowth (Real.exp 1))
    {r : ℝ} (hr : r ≤ Real.exp 1 + 1) : extendedFunction B r = r := by
  simp [extendedFunction, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr)]

theorem extendedFunction_eq (B : AdmissibleGrowth (Real.exp 1))
    {r : ℝ} (hr : Real.exp 1 + 2 ≤ r) : extendedFunction B r = B.B r := by
  rw [extendedFunction, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

/-- Smoothness uses the old function only in the open region r>e. -/
theorem extendedFunction_contDiff (B : AdmissibleGrowth (Real.exp 1)) :
    ContDiff ℝ ∞ (extendedFunction B) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r < Real.exp 1 + 1
  · apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hr] with s hs
    exact extendedFunction_eq_id B (le_of_lt hs)
  · have he : Real.exp 1 < r := by linarith
    have hB := B.smooth.contDiffAt (Ici_mem_nhds he)
    exact contDiffAt_id.add
      ((Real.smoothTransition.contDiffAt.comp r
        (contDiffAt_id.sub contDiffAt_const)).mul (hB.sub contDiffAt_id))

theorem extendedFunction_dominates (B : AdmissibleGrowth (Real.exp 1))
    (r : ℝ) : r ≤ extendedFunction B r := by
  by_cases hr : r ≤ Real.exp 1 + 1
  · rw [extendedFunction_eq_id B hr]
  · have hb : r ≤ B.B r := B.dominates r (by simp only [mem_Ici]; linarith)
    exact le_add_of_nonneg_right
      (mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr hb))

theorem extendedFunction_positive (B : AdmissibleGrowth (Real.exp 1))
    {r : ℝ} (hr : 1 ≤ r) : 0 < extendedFunction B r := by
  exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hr) (extendedFunction_dominates B r)

/-- Native finite-interval integrability, including the source endpoint. -/
theorem admissible_integrable {a : ℝ} (B : AdmissibleGrowth a)
    {u v : ℝ} (hu : a ≤ u) (hv : a ≤ v) :
    IntervalIntegrable (fun r => r / (B.B r)^2) volume u v := by
  apply ContinuousOn.intervalIntegrable
  have hsub : uIcc u v ⊆ Ici a := by
    intro r hr
    exact le_trans (le_min hu hv) hr.1
  exact continuousOn_id.div ((B.smooth.continuousOn.mono hsub).pow 2)
    (fun r hr => pow_ne_zero 2 (B.positive r (hsub hr)).ne')

theorem extendedFunction_integrable (B : AdmissibleGrowth (Real.exp 1))
    {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    IntervalIntegrable (fun r => r / (extendedFunction B r)^2) volume u v := by
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_id.div ((extendedFunction_contDiff B).continuous.continuousOn.pow 2)
    (fun r hr => pow_ne_zero 2 (extendedFunction_positive B
      (le_trans (le_min hu hv) hr.1)).ne')

/-- Above the cutoff the two literal primitives differ by a finite constant. -/
theorem primitive_eq_add_constant (B : AdmissibleGrowth (Real.exp 1))
    {b : ℝ} (hb : Real.exp 1 + 2 ≤ b) :
    (∫ r in 1..b, r / (extendedFunction B r)^2) =
      (∫ r in (Real.exp 1)..b, r / (B.B r)^2) +
      ((∫ r in 1..(Real.exp 1 + 2), r / (extendedFunction B r)^2) -
       (∫ r in (Real.exp 1)..(Real.exp 1 + 2), r / (B.B r)^2)) := by
  have he := Real.exp_pos (1 : ℝ)
  have hnew := intervalIntegral.integral_add_adjacent_intervals
    (extendedFunction_integrable B (le_refl 1) (by linarith : 1 ≤ Real.exp 1 + 2))
    (extendedFunction_integrable B (by linarith : 1 ≤ Real.exp 1 + 2)
      (by linarith : 1 ≤ b))
  have hold := intervalIntegral.integral_add_adjacent_intervals
    (admissible_integrable B (le_refl _) (by linarith : Real.exp 1 ≤ Real.exp 1 + 2))
    (admissible_integrable B (by linarith : Real.exp 1 ≤ Real.exp 1 + 2)
      (by linarith : Real.exp 1 ≤ b))
  have htail : (∫ r in (Real.exp 1 + 2)..b, r / (extendedFunction B r)^2) =
      ∫ r in (Real.exp 1 + 2)..b, r / (B.B r)^2 := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hb] at hr
    dsimp only
    rw [extendedFunction_eq B hr.1]
  linarith

theorem extendedFunction_divergent (B : AdmissibleGrowth (Real.exp 1)) :
    Tendsto (fun b : ℝ => ∫ r in 1..b, r / (extendedFunction B r)^2) atTop atTop := by
  have h := tendsto_atTop_add_const_right atTop
    ((∫ r in 1..(Real.exp 1 + 2), r / (extendedFunction B r)^2) -
     (∫ r in (Real.exp 1)..(Real.exp 1 + 2), r / (B.B r)^2)) B.divergent
  apply h.congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1 + 2)] with b hb
  exact (primitive_eq_add_constant B hb).symm

/-- The actual admissible growth witness on the radial half-line. -/
def extend (B : AdmissibleGrowth (Real.exp 1)) : AdmissibleGrowth 1 where
  B := extendedFunction B
  smooth := (extendedFunction_contDiff B).contDiffOn
  positive := fun _ hr => extendedFunction_positive B hr
  dominates := fun r _ => extendedFunction_dominates B r
  divergent := extendedFunction_divergent B

theorem extend_eq (B : AdmissibleGrowth (Real.exp 1))
    {r : ℝ} (hr : Real.exp 1 + 2 ≤ r) : (extend B).B r = B.B r :=
  extendedFunction_eq B hr

theorem extend_eventuallyEq (B : AdmissibleGrowth (Real.exp 1)) :
    (extend B).B =ᶠ[atTop] B.B := by
  filter_upwards [eventually_ge_atTop (Real.exp 1 + 2)] with r hr
  exact extend_eq B hr

theorem scalarTarget : ScalarTarget := fun B => ⟨extend B, fun _ hr => extend_eq B hr⟩

end ExactLiouvilleComparison.SteinGrowth
