import ExactLiouvilleComparison.ODEGlobalField

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Rescale the proved closed-interval theorem to an arbitrary finite horizon,
then assemble genuine suspended native curves by Mathlib uniqueness. -/
theorem global_solution_of_scalar_bound
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P)
    (hp : IsProperMap P) (hl : BddBelow (range P))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ t x, |M.scalarDerivative P x (Z t x)| ≤ D)
    (s : ℝ) (x : M.Point) :
    ∃ γ : ℝ → M.Point, γ s = x ∧ ∀ t,
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))) := by
  have hv := CollarFlow.contMDiff_timeSuspension hZ
  have hex : ∀ a : ℝ, ∃ α : ℝ → ℝ × M.Point, α 0 = (s,x) ∧
      IsMIntegralCurveOn α (CollarFlow.timeSuspension Z) (Ioo (-a) a) := by
    intro a
    let b := |a| + 1
    have hbpos : 0 < b := by dsimp [b]; positivity
    have hbne : (2*b) ≠ 0 := ne_of_gt (by positivity)
    let Y : ℝ → (y : M.Point) → M.Tangent y := fun t y => (2*b) • Z (s-b+2*b*t) y
    have hc : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × M.Point => (s-b+2*b*p.1,p.2)) :=
      (contMDiff_const.add (contMDiff_const.mul contMDiff_fst)).prodMk contMDiff_snd
    have hY := contMDiff_cutoff_field (fun t => Z (s-b+2*b*t)) isOpen_univ
      (hZ.comp hc).contMDiffOn (fun _ => 2*b) contMDiff_const (subset_univ _)
    have hbound : ∀ t ∈ parameterInterval, ∀ y,
        |M.scalarDerivative P y (Y t y)| ≤ (2*b)*D := by
      intro t _ y
      simp only [Y, scalarDerivative, map_smul, smul_eq_mul, abs_mul,
        abs_of_pos (show 0 < 2*b by positivity)]
      exact mul_le_mul_of_nonneg_left (hb _ _) (by positivity)
    obtain ⟨γ, hinit, hγ⟩ := finiteIntervalExistence Y univ isOpen_univ (subset_univ _)
      hY.contMDiffOn P hP hp hl ((2*b)*D) (by positivity) hbound
      ⟨1/2, by constructor <;> norm_num⟩ x
    let α : ℝ → ℝ × M.Point := fun u => (s+u, γ ((u+b)/(2*b)))
    have hαzero : α 0 = (s,x) := by
      have he : (0+b)/(2*b) = (1/2 : ℝ) := by field_simp; ring
      simp only [α, add_zero, he, hinit]
    refine ⟨α, hαzero, ?_⟩
    intro u hu
    have huba : -b < u ∧ u < b := by
      have hab : a < b := by dsimp [b]; linarith [le_abs_self a]
      constructor <;> linarith [hu.1,hu.2]
    have hq : (u+b)/(2*b) ∈ parameterInterval := by
      constructor
      · apply div_nonneg <;> linarith [huba.1]
      · apply (div_le_one (by positivity : 0 < 2*b)).mpr
        linarith [huba.2]
    have ht : s-b+2*b*((u+b)/(2*b)) = s+u := by field_simp; ring
    have haff : HasDerivAt (fun v : ℝ => (v+b)/(2*b)) (1/(2*b)) u := by
      simpa using ((hasDerivAt_id u).add_const b).div_const (2*b)
    have hd := (hγ _ hq).comp u haff.hasFDerivAt.hasMFDerivAt
    have hsp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun v => γ ((v+b)/(2*b))) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (s+u) (γ ((u+b)/(2*b))))) := by
      apply hd.congr_mfderiv
      apply ContinuousLinearMap.ext
      intro r
      change ℝ at r
      change ((r * (1/(2*b))) • ((2*b) • Z (s-b+2*b*((u+b)/(2*b))) _)) = r • Z (s+u) _
      rw [ht, smul_smul]
      congr 1
      field_simp
    have htime : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun v : ℝ => s+v) u
        (1 : ℝ →L[ℝ] ℝ) := by
      convert ((hasDerivAt_id u).const_add s).hasFDerivAt.hasMFDerivAt using 1 <;> ext <;> simp
    apply HasMFDerivAt.hasMFDerivWithinAt
    apply (htime.prodMk hsp).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    change (r, r • Z (s+u) (γ ((u+b)/(2*b)))) = r • ((1 : ℝ), Z (s+u) (γ ((u+b)/(2*b))))
    simp
  obtain ⟨α, hα₀, hα⟩ :=
    (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo
      (hv.of_le (by simp)) (s,x)).mpr hex
  let β : ℝ → ℝ × M.Point := α ∘ (· - s)
  have hβ : IsMIntegralCurve β (CollarFlow.timeSuspension Z) := isMIntegralCurve_comp_sub.mpr hα
  have hβ₀ : β s = (s,x) := by simp only [β, comp_apply, sub_self, hα₀]
  have htime : ∀ t : ℝ, HasDerivAt (fun u => (β u).1) (1 : ℝ) t := by
    intro t
    have hf := (hasMFDerivAt_fst (β t)).comp t (hβ t)
    apply (hasMFDerivAt_iff_hasFDerivAt.mp hf).hasDerivAt.congr_deriv
    change (1 : ℝ) • (1 : ℝ) = 1
    simp
  have htimeEq : (fun u => (β u).1) = id := by
    apply ODE_solution_unique_univ (t₀ := s)
      (v := fun (_ : ℝ) (_ : ℝ) => (1 : ℝ)) (s := fun _ => univ) (K := 0)
      (fun _ => (LipschitzWith.const 1).lipschitzOnWith)
    · exact fun t => ⟨htime t, mem_univ _⟩
    · exact fun t => ⟨hasDerivAt_id t, mem_univ _⟩
    · exact congrArg Prod.fst hβ₀
  refine ⟨fun t => (β t).2, congrArg Prod.snd hβ₀, ?_⟩
  intro t
  have hs := (hasMFDerivAt_snd (β t)).comp t (hβ t)
  apply hs.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  simp [CollarFlow.timeSuspension, congrFun htimeEq t]
  rfl
end ExactLiouvilleComparison.ODE
