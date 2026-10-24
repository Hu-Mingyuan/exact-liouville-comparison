import ExactLiouvilleComparison.ODETwoBarrierStatement
import ExactLiouvilleComparison.ODEScalarConfinement
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Two one-sided estimates for actual native curves, stable under bounded cutoffs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Multiplication by a number in `[0,1]` preserves a nonnegative upper rate bound. -/
theorem twoBarrier_forward_cutoff (R : M.Point → ℝ) (x : M.Point)
    (v : M.Tangent x) {c C : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hC : 0 ≤ C) (hv : M.scalarDerivative R x v ≤ C) :
    M.scalarDerivative R x (c • v) ≤ C := by
  simp only [scalarDerivative, map_smul, smul_eq_mul] at *
  exact (mul_le_mul_of_nonneg_left hv hc.1).trans (mul_le_of_le_one_left hC hc.2)

/-- The nonnegative partial time rate is exactly what makes the reverse bound
stable under a cutoff; no absolute bound on the spatial rate is used. -/
theorem twoBarrier_reverse_cutoff (Q : ℝ → M.Point → ℝ) (t : ℝ) (x : M.Point)
    (v : M.Tangent x) {c C : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hC : 0 ≤ C)
    (ht : 0 ≤ deriv (fun u => Q u x) t)
    (hv : -C ≤ deriv (fun u => Q u x) t + M.scalarDerivative (Q t) x v) :
    -C ≤ deriv (fun u => Q u x) t + M.scalarDerivative (Q t) x (c • v) := by
  have hmul := mul_le_mul_of_nonneg_left hv hc.1
  have hpos := mul_nonneg (sub_nonneg.mpr hc.2) ht
  have hconst := mul_nonneg (sub_nonneg.mpr hc.2) hC
  have he : M.scalarDerivative (Q t) x (c • v) = c * M.scalarDerivative (Q t) x v := by
    simp only [scalarDerivative, map_smul, smul_eq_mul]
  rw [he]
  nlinarith

/-- The derivative of a moving barrier along a native curve is the sum of its
ordinary partial time derivative and its native spatial derivative. -/
theorem twoBarrier_hasDerivAt
    (Q : ℝ → M.Point → ℝ)
    (hQ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => Q p.1 p.2))
    {γ : ℝ → M.Point} {t : ℝ} {v : M.Tangent (γ t)}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasDerivAt (fun u => Q u (γ u))
      (deriv (fun u => Q u (γ t)) t + M.scalarDerivative (Q t) (γ t) v) t := by
  have hpair := (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t).prodMk hγ
  have hdiff := hQ.mdifferentiable (by simp) (t, γ t)
  have hd := (hasMFDerivAt_iff_hasFDerivAt.mp
    (hdiff.hasMFDerivAt.comp t hpair)).hasDerivAt
  apply hd.congr_deriv
  change (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ)
    (fun p : ℝ × M.Point => Q p.1 p.2) (t, γ t)) (1, (1 : ℝ) • v) = _
  rw [one_smul, mfderiv_prod_eq_add_apply hdiff]
  simp only [scalarDerivative, mfderiv_eq_fderiv]
  rfl

/-- An upper rate bound controls forward displacement on the closed parameter interval. -/
theorem twoBarrier_forward_displacement {f f' : ℝ → ℝ} {C : ℝ}
    (hf : ∀ u ∈ parameterInterval, HasDerivAt f (f' u) u)
    (hb : ∀ u ∈ parameterInterval, f' u ≤ C)
    {s t : ℝ} (hs : s ∈ parameterInterval) (ht : t ∈ parameterInterval) (hst : s ≤ t) :
    f t ≤ f s + C * (t - s) := by
  have h := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun u hu => (hf u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hf u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by rw [(hf u (interior_subset hu)).deriv]; exact hb u (interior_subset hu))
    s hs t ht hst
  linarith

/-- A lower total rate bound controls the moving barrier in reverse time. -/
theorem twoBarrier_reverse_displacement {f f' : ℝ → ℝ} {C : ℝ}
    (hf : ∀ u ∈ parameterInterval, HasDerivAt f (f' u) u)
    (hb : ∀ u ∈ parameterInterval, -C ≤ f' u)
    {s t : ℝ} (hs : s ∈ parameterInterval) (ht : t ∈ parameterInterval) (hts : t ≤ s) :
    f t ≤ f s + C * (s - t) := by
  have h := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    (fun u hu => (hf u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hf u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by rw [(hf u (interior_subset hu)).deriv]; exact hb u (interior_subset hu))
    t ht s hs hts
  linarith


/-- A spatial scalar differentiated along a full native trajectory. -/
theorem twoBarrier_spatial_hasDerivAt
    (R : M.Point → ℝ) (hR : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ R)
    {γ : ℝ → M.Point} {t : ℝ} {v : M.Tangent (γ t)}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasDerivAt (fun u => R (γ u)) (M.scalarDerivative R (γ t) v) t := by
  have hd := ((hR.mdifferentiable (by simp) (γ t)).hasMFDerivAt.comp t hγ)
  apply (hasMFDerivAt_iff_hasFDerivAt.mp hd).hasDerivAt.congr_deriv
  change M.scalarDerivative R (γ t) ((1 : ℝ) • v) = _
  rw [one_smul]

/-- A compact set is chosen from the initial data before any cutoff or trajectory.
It confines every field with the two rate bounds, forward by R and backward by Q. -/
theorem twoBarrier_compact_confinement
    (R : M.Point → ℝ) (hR : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ R)
    (hp : IsProperMap R) (hl : BddBelow (range R))
    (Q : ℝ → M.Point → ℝ)
    (hQ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => Q p.1 p.2))
    (hcontrol : ∀ L : ℝ, ∃ A : ℝ, ∀ t ∈ parameterInterval, ∀ x, Q t x ≤ L → R x ≤ A)
    {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (s : Parameter) (x : M.Point) :
    ∃ K : Set M.Point, IsCompact K ∧
      ∀ W : ℝ → (y : M.Point) → M.Tangent y,
        (∀ t ∈ parameterInterval, ∀ y, M.scalarDerivative R y (W t y) ≤ C₀) →
        (∀ t ∈ parameterInterval, ∀ y,
          -C₁ ≤ deriv (fun u => Q u y) t + M.scalarDerivative (Q t) y (W t y)) →
        ∀ γ : ℝ → M.Point, γ s.val = x →
          (∀ t ∈ parameterInterval, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (W t (γ t)))) →
          ∀ t ∈ parameterInterval, γ t ∈ K := by
  obtain ⟨A, hA⟩ := hcontrol (Q s.val x + C₁)
  refine ⟨{y | R y ≤ max (R x + C₀) A}, compact_sublevel R hp hl _, ?_⟩
  intro W hforward hreverse γ hinit hγ t ht
  change R (γ t) ≤ max (R x + C₀) A
  rcases le_total s.val t with hst | hts
  · have h := twoBarrier_forward_displacement
      (fun u hu => twoBarrier_spatial_hasDerivAt R hR (hγ u hu))
      (fun u hu => hforward u hu (γ u)) s.property ht hst
    rw [hinit] at h
    have htime : t - s.val ≤ 1 := by linarith [ht.2, s.property.1]
    have hbound := mul_le_mul_of_nonneg_left htime hC₀
    exact (show R (γ t) ≤ R x + C₀ by linarith).trans (le_max_left _ _)
  · have h := twoBarrier_reverse_displacement
      (fun u hu => twoBarrier_hasDerivAt Q hQ (hγ u hu))
      (fun u hu => hreverse u hu (γ u)) s.property ht hts
    rw [hinit] at h
    have htime : s.val - t ≤ 1 := by linarith [s.property.2, ht.1]
    have hbound := mul_le_mul_of_nonneg_left htime hC₁
    exact (hA t ht (γ t) (by linarith)).trans (le_max_right _ _)

end ExactLiouvilleComparison.ODE
