import ExactLiouvilleComparison.RadialInterpolationGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.RadialInterpolation
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}

/-- The sharp dual estimate in the delivered h metric. No nonzero-dR hypothesis. -/
theorem differential_sq_le (q : RadialCoefficient P.rstar) (x : M.Point)
    (hx : P.rstar < P.R x) (v : q.compatible.MetricTangent x) :
    (M.scalarDerivative P.R x v)^2 ≤
      (q.radialA x / (P.c * q.radialD x)) * ‖v‖^2 := by
  let l := q.compatible.covector x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)
  have h := (sq_le_sq₀ (norm_nonneg (l v))
    (mul_nonneg (norm_nonneg l) (norm_nonneg v))).2 (l.le_opNorm v)
  rw [mul_pow] at h
  have he : ‖l‖^2 = q.radialA x / (P.c * q.radialD x) := q.radial_dualNorm_sq x hx
  rw [he] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  convert h using 1
  rfl

theorem radial (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (δ : ℝ → ℝ) (x : M.Point) (hx : P.rstar < P.R x) (hδ : 0 ≤ δ (P.R x)) :
    0 ≤ -M.scalarDerivative P.R x (vector q σ hσ hw δ x) ∧
    -M.scalarDerivative P.R x (vector q σ hσ hw δ x) ≤ δ (P.R x) * q.radialA x / q.radialD x := by
  let X := vector q σ hσ hw δ x
  let Y := -M.scalarDerivative P.R x X
  have hc := P.positive_c
  have hD := q.radialD_pos x hx
  have ha := q.radialA_nonneg x
  rcases eq_or_lt_of_le hδ with hz | hp
  · have hX := vector_eq_zero q σ hσ hw δ x hz.symm
    simp [hX, hz.symm, scalarDerivative]
  have he := energy q σ hσ hw δ x hx
  have hs := hw x X
  have hn := sq_nonneg (@norm (q.compatible.MetricTangent x) _ X)
  have henergy : @norm (q.compatible.MetricTangent x) _ X ^ 2 ≤ P.c * δ (P.R x) * Y := by
    dsimp [Y, X] at *
    linarith
  have hY : 0 ≤ Y := by
    have hh : 0 ≤ P.c * δ (P.R x) * Y := hn.trans henergy
    exact (mul_nonneg_iff_of_pos_left (mul_pos hc hp)).mp hh
  refine ⟨hY, ?_⟩
  have hCS := differential_sq_le q x hx X
  have hmul := mul_le_mul_of_nonneg_left henergy (div_nonneg ha (mul_pos hc hD).le)
  have hid : q.radialA x / (P.c * q.radialD x) * (P.c * δ (P.R x) * Y) =
      (δ (P.R x) * q.radialA x / q.radialD x) * Y := by
    field_simp
  have hsq : Y^2 ≤ (δ (P.R x) * q.radialA x / q.radialD x) * Y := by
    rw [hid] at hmul
    have hCs' : Y^2 ≤ q.radialA x / (P.c * q.radialD x) *
        @norm (q.compatible.MetricTangent x) _ X ^ 2 := by
      simpa only [Y, neg_sq] using hCS
    exact hCs'.trans hmul
  change Y ≤ _
  rcases eq_or_lt_of_le hY with hz | hpY
  · rw [← hz]; exact div_nonneg (mul_nonneg hδ ha) hD.le
  · nlinarith

/-- Pointwise Qmonotone expression. No trajectory is supplied or assumed. -/
theorem Q_directional (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (x : M.Point) (hx : P.rstar < P.R x) :
    let q := coefficient q₀ q₁ u hu
    let δ := delta q₀ q₁ (P.R x)
    let XR := M.scalarDerivative P.R x (vector q σ hσ hw (delta q₀ q₁) x)
    δ * q.rho (P.R x) * (P.R x - q.radialA x) / q.radialD x ≤
      δ * P.R x + (q.rho (P.R x) + P.R x * q.rhoPrime (P.R x)) * XR ∧
    0 ≤ δ * q.rho (P.R x) * (P.R x - q.radialA x) / q.radialD x := by
  dsimp only
  let q := coefficient q₀ q₁ u hu
  let δ := delta q₀ q₁ (P.R x)
  let XR := M.scalarDerivative P.R x (vector q σ hσ hw (delta q₀ q₁) x)
  have hδ : 0 ≤ δ := sub_nonneg.mpr (horder _ (P.lower_R x))
  have hD := q.radialD_pos x hx
  have hm := q.radial_positive (P.R x) (P.lower_R x)
  change 0 < q.rho (P.R x) + P.R x * q.rhoPrime (P.R x) at hm
  have hr := (radial q σ hσ hw (delta q₀ q₁) x hx hδ).2
  change -XR ≤ δ * q.radialA x / q.radialD x at hr
  have hh := mul_le_mul_of_nonneg_left hr hm.le
  have hid :
      δ * q.rho (P.R x) * (P.R x - q.radialA x) / q.radialD x =
      δ * P.R x - (q.rho (P.R x) + P.R x * q.rhoPrime (P.R x)) *
        (δ * q.radialA x / q.radialD x) := by
    field_simp
    dsimp [RadialCoefficient.radialD]
    ring
  constructor
  · change _ ≤ δ * P.R x + _ * XR
    rw [hid]
    linarith
  · exact div_nonneg (mul_nonneg (mul_nonneg hδ (q.positive _ (P.lower_R x)).le)
      (sub_nonneg.mpr (P.radial_bound x hx))) hD.le

end ExactLiouvilleComparison.RadialInterpolation
