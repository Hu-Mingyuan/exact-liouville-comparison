import ExactLiouvilleComparison.LargeCoefficientNorm
import ExactLiouvilleComparison.LargeCoefficientSeries
import ExactLiouvilleComparison.SmallCoefficientK

/-! Manuscript Mn, A and Aproperties for an arbitrary native smooth one-form. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.LargeCoefficient
variable {d : ℕ} {M : SmoothManifold d}

def sublevel (P : RadialReference M) (n : ℕ) : Set M.Point :=
  {x | P.R x ≤ P.rstar + n + 1}

theorem sublevel_compact (P : RadialReference M) (n : ℕ) :
    IsCompact (sublevel P n) := by
  have heq : sublevel P n = P.R ⁻¹' Icc 1 (P.rstar + n + 1) := by
    ext x
    exact (and_iff_right (P.lower_R x)).symm
  rw [heq]
  exact P.proper_R.isCompact_preimage isCompact_Icc

theorem sublevel_mono (P : RadialReference M) : Monotone (sublevel P) := by
  intro n m hnm x hx
  have : (n : ℝ) ≤ m := by exact_mod_cast hnm
  change P.R x ≤ P.rstar + n + 1 at hx
  change P.R x ≤ P.rstar + m + 1
  linarith

def levels (P : RadialReference M) (lam : M.Form 1) (n : ℕ) : ℝ :=
  1 + sSup (formNorm P.compatible lam '' sublevel P n)

theorem sublevel_norm_bddAbove (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (n : ℕ) :
    BddAbove (formNorm P.compatible lam '' sublevel P n) :=
  formNorm_bddAbove_on_compact P.compatible lam hlam (sublevel_compact P n)

theorem one_le_levels (P : RadialReference M) (lam : M.Form 1) (n : ℕ) :
    1 ≤ levels P lam n := by
  apply le_add_of_nonneg_right
  apply Real.sSup_nonneg
  rintro z ⟨x, _, rfl⟩
  exact formNorm_nonneg P.compatible lam x

theorem levels_empty (P : RadialReference M) (lam : M.Form 1) (n : ℕ)
    (hn : sublevel P n = ∅) : levels P lam n = 1 := by
  simp [levels, hn, Real.sSup_empty]

theorem levels_mono (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) : Monotone (levels P lam) := by
  intro n m hnm
  by_cases h : (sublevel P n).Nonempty
  · apply add_le_add_right
    exact csSup_le_csSup (sublevel_norm_bddAbove P lam hlam m)
      (h.image _) (image_mono (sublevel_mono P hnm))
  · rw [levels_empty P lam n (not_nonempty_iff_eq_empty.mp h)]
    exact one_le_levels P lam m

theorem norm_le_levels (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (n : ℕ) {x : M.Point} (hx : x ∈ sublevel P n) :
    1 + formNorm P.compatible lam x ≤ levels P lam n :=
  add_le_add_right (le_csSup (sublevel_norm_bddAbove P lam hlam n) (mem_image_of_mem _ hx)) 1

def A (P : RadialReference M) (lam : M.Form 1) : ℝ → ℝ :=
  series (levels P lam) P.rstar

/-- Equation A with the manuscript index `j = n + 1`. -/
theorem A_formula (P : RadialReference M) (lam : M.Form 1) (r : ℝ) :
    A P lam r = levels P lam 0 + ∑' n : ℕ,
      (levels P lam (n + 1) - levels P lam n) *
        Real.smoothTransition (r - P.rstar - (n + 1) + 1) := by
  unfold A series stepTerm SmallCoefficient.chi
  congr 1
  apply tsum_congr
  intro n
  congr 2
  ring

theorem A_locally_finite (P : RadialReference M) (lam : M.Form 1) (r : ℝ) :
    ∃ N : ℕ, ∀ᶠ s in 𝓝 r, ∀ n, N ≤ n →
      stepTerm (levels P lam) P.rstar n s = 0 :=
  series_locally_finite _ _ _

theorem A_smooth (P : RadialReference M) (lam : M.Form 1) :
    ContDiff ℝ ∞ (A P lam) := series_smooth _ _

theorem A_core (P : RadialReference M) (lam : M.Form 1) {r : ℝ} (hr : r ≤ P.rstar) :
    A P lam r = levels P lam 0 := series_eq_core _ _ hr

theorem A_monotone (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) : Monotone (A P lam) :=
  series_monotone (levels_mono P lam hlam) _

theorem A_deriv_nonneg (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (r : ℝ) : 0 ≤ deriv (A P lam) r :=
  series_deriv_nonneg (levels_mono P lam hlam) _ _

theorem one_le_A (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (r : ℝ) : 1 ≤ A P lam r :=
  (one_le_levels P lam 0).trans (series_ge_zero_term (levels_mono P lam hlam) _ _)

theorem A_radial_pos (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) {r : ℝ} (hr : 1 ≤ r) :
    0 < A P lam r + r * deriv (A P lam) r :=
  series_radial_pos (levels_mono P lam hlam) (one_le_levels P lam 0) _ hr

theorem A_dominates (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (x : M.Point) :
    1 + P.compatible.dualNorm x (oneCovector lam x) ≤ A P lam (P.R x) := by
  by_cases hx : P.R x ≤ P.rstar
  · rw [A_core P lam hx]
    apply norm_le_levels P lam hlam 0
    change P.R x ≤ P.rstar + (0 : ℕ) + 1
    simp only [Nat.cast_zero, add_zero]
    linarith
  · have hnonneg : 0 ≤ P.R x - P.rstar := by linarith
    let n := ⌊P.R x - P.rstar⌋₊
    have hn : (n : ℝ) ≤ P.R x - P.rstar := Nat.floor_le hnonneg
    have hn' : P.R x - P.rstar < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    apply (norm_le_levels P lam hlam n (show x ∈ sublevel P n by
      change P.R x ≤ P.rstar + n + 1; linarith)).trans
    exact series_ge_level (levels_mono P lam hlam) _ n (by linarith)

theorem k_le_A (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (G : AdmissibleGrowth 1) {r : ℝ} (hr : 1 ≤ r) :
    SmallCoefficient.k G P.rstar r ≤ A P lam r :=
  (SmallCoefficient.k_le_one G P.rstar hr).trans (one_le_A P lam hlam r)

/-- The actual constructed coefficient, requiring only smoothness of the primitive.
No symplecticity, inverse bound, growth bound, or completeness is needed. -/
theorem coefficient_properties (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) :
    ContDiff ℝ ∞ (A P lam) ∧ Monotone (A P lam) ∧
    (∀ r ∈ Icc 1 P.rstar, A P lam r = levels P lam 0) ∧
    (∀ r, 0 ≤ deriv (A P lam) r) ∧
    (∀ r, 1 ≤ A P lam r) ∧
    (∀ r, 1 ≤ r → 0 < A P lam r + r * deriv (A P lam) r) ∧
    (∀ x, 1 + P.compatible.dualNorm x (oneCovector lam x) ≤ A P lam (P.R x)) :=
  ⟨A_smooth P lam, A_monotone P lam hlam, fun _ hr => A_core P lam hr.2,
    A_deriv_nonneg P lam hlam, one_le_A P lam hlam,
    fun _ hr => A_radial_pos P lam hlam hr, A_dominates P lam hlam⟩

end ExactLiouvilleComparison.LargeCoefficient
