import ExactLiouvilleComparison.ThirdPathStatement
import ExactLiouvilleComparison.MoserRegularityCompact
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Scalar control for the literal third-path exhaustion. The vector field is arbitrary;
the parent construction supplies its native joint regularity and reference-metric bound.
No flow or completeness assumption occurs in these lemmas. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ThirdPath
variable {d : ℕ} {M : SmoothManifold d}

theorem exhaustion_smooth (P : RadialReference M) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (exhaustion P) := by
  intro x
  have hs := Real.contDiffAt_sqrt (n := ∞)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (P.lower_R x)))
  exact hs.comp_contMDiffAt (P.smooth_R x)

theorem exhaustion_lower (P : RadialReference M) (x : M.Point) :
    1 ≤ exhaustion P x := by
  simpa only [exhaustion, Real.sqrt_one] using Real.sqrt_le_sqrt (P.lower_R x)

theorem exhaustion_bddBelow (P : RadialReference M) :
    BddBelow (range (exhaustion P)) :=
  ⟨1, by rintro _ ⟨x, rfl⟩; exact exhaustion_lower P x⟩

theorem exhaustion_proper (P : RadialReference M) :
    IsProperMap (exhaustion P) := by
  apply isProperMap_of_comp_of_t2 (exhaustion_smooth P).continuous
    (continuous_id.pow 2)
  change IsProperMap ((fun r : ℝ => r ^ 2) ∘ exhaustion P)
  have he : (fun r : ℝ => r ^ 2) ∘ exhaustion P = P.R := by
    funext x
    exact Real.sq_sqrt (le_trans zero_le_one (P.lower_R x))
  rw [he]
  exact P.proper_R

theorem exhaustion_derivative (P : RadialReference M) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (exhaustion P) x v =
      (1 / (2 * Real.sqrt (P.R x))) * M.scalarDerivative P.R x v := by
  have h := (Real.hasDerivAt_sqrt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (P.lower_R x)))).hasFDerivAt.hasMFDerivAt.comp x
    (P.smooth_R.mdifferentiable (by simp) x).hasMFDerivAt
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (exhaustion P) x v = _
  rw [show exhaustion P = Real.sqrt ∘ P.R from rfl, h.mfderiv]
  change M.scalarDerivative P.R x v * _ = _
  ring

/-- The exterior estimate uses only the radial dual-norm bound at this point.
The norm premise is explicitly the reference g norm, not the chart norm. -/
theorem exhaustion_exterior_bound (P : RadialReference M) (x : M.Point)
    (hx : P.rstar < P.R x) (v : M.Tangent x)
    (hv : @norm (P.compatible.MetricTangent x) _ v ≤ 1) :
    |M.scalarDerivative (exhaustion P) x v| ≤ 1 / (2 * Real.sqrt P.c) := by
  let D := P.compatible.dualNorm x (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) P.R x)
  have hD : 0 ≤ D := norm_nonneg _
  have hR : 0 < P.R x := lt_of_lt_of_le zero_lt_one (P.lower_R x)
  have hsR : 0 < Real.sqrt (P.R x) := Real.sqrt_pos.mpr hR
  have hsc : 0 < Real.sqrt P.c := Real.sqrt_pos.mpr P.positive_c
  have hd : |M.scalarDerivative P.R x v| ≤ D := by
    calc
      _ ≤ D * @norm (P.compatible.MetricTangent x) _ v :=
        (P.compatible.covector x (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) P.R x)).le_opNorm v
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hv hD
      _ = D := mul_one D
  have hb : Real.sqrt P.c * D ≤ Real.sqrt (P.R x) := by
    have hr := P.radial_bound x hx
    change P.c * D ^ 2 ≤ P.R x at hr
    have he : (Real.sqrt P.c * D) ^ 2 ≤ (Real.sqrt (P.R x)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt P.positive_c.le, Real.sq_sqrt hR.le]
      exact hr
    nlinarith [mul_nonneg hsc.le hD]
  rw [exhaustion_derivative, abs_mul, abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num) hsR))]
  calc
    _ ≤ (1 / (2 * Real.sqrt (P.R x))) * D :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ 1 / (2 * Real.sqrt P.c) := by
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ (mul_pos (by norm_num) hsc)).mpr
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (mul_pos (by norm_num) hsR)).mpr
      nlinarith [hb]

theorem exhaustion_core_bound (P : RadialReference M)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : MoserRegularity.NativeJoint Z) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s x, P.R x ≤ P.rstar →
      |M.scalarDerivative (exhaustion P) x (Z s x)| ≤ D :=
  hZ.compact_scalar_bound (exhaustion P) (exhaustion_smooth P) _
    (MoserRegularity.core_compact P)

theorem exhaustion_global_bound (P : RadialReference M)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : MoserRegularity.NativeJoint Z)
    (hZnorm : ∀ s x, @norm (P.compatible.MetricTangent x) _ (Z s x) ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s x,
      |M.scalarDerivative (exhaustion P) x (Z s x)| ≤ D := by
  obtain ⟨D, hD, hb⟩ := exhaustion_core_bound P hZ
  refine ⟨max D (1 / (2 * Real.sqrt P.c)), hD.trans (le_max_left _ _), ?_⟩
  intro s x
  by_cases hx : P.R x ≤ P.rstar
  · exact (hb s x hx).trans (le_max_left _ _)
  · exact (exhaustion_exterior_bound P x (lt_of_not_ge hx) (Z s x) (hZnorm s x)).trans
      (le_max_right _ _)

end ExactLiouvilleComparison.ThirdPath
