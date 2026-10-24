import ExactLiouvilleComparison.ODEContinuation

/-! A constructed all-real auxiliary field, equal to the input on the closed strip. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

theorem smooth_scalar_rate (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => M.scalarDerivative P p.2 (Z p.1 p.2)) := by
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp
    ((hP.contMDiff_tangentMap (by simp)).comp hZ)

/-- Global smooth extension of the section, with equality on the closed strip.
The separating cutoff need not have compact support. -/
theorem extend_strip_field (Z : ℝ → (x : M.Point) → M.Tangent x)
    {Ω : Set (ℝ × M.Point)} (hΩ : IsOpen Ω) (hstrip : parameterInterval ×ˢ univ ⊆ Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω) :
    ∃ W : ℝ → (x : M.Point) → M.Tangent x,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun p : ℝ × M.Point => (⟨p.2, W p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) ∧
      ∀ t ∈ parameterInterval, W t = Z t := by
  let := ChartedSpace.locallyCompactSpace (Model d) M.Point
  let : LocallyCompactSpace (ModelProd ℝ (Model d)) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × Model d))
  have hclosed : IsClosed (parameterInterval ×ˢ (univ : Set M.Point)) :=
    isClosed_Icc.prod isClosed_univ
  obtain ⟨U, hU, hKU, hUΩ⟩ := normal_exists_closure_subset hclosed hΩ hstrip
  obtain ⟨χ, hχ, _, hsupport, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (n := ⊤) hU hclosed hKU
  have hsupp : tsupport χ ⊆ Ω := by simpa only [tsupport, hsupport] using hUΩ
  refine ⟨fun t x => χ (t,x) • Z t x, contMDiff_cutoff_field Z hΩ hZ χ hχ hsupp, ?_⟩
  intro t ht
  funext x
  change χ (t,x) • Z t x = Z t x
  rw [(hone (t,x)).mp ⟨ht, mem_univ x⟩, one_smul]

/-- Cap the scalar rate outside the closed strip, leaving the input field exactly
unchanged on it. No bound on the original off-strip field is assumed. -/
theorem globally_bounded_extension (Z : ℝ → (x : M.Point) → M.Tangent x)
    {Ω : Set (ℝ × M.Point)} (hΩ : IsOpen Ω) (hstrip : parameterInterval ×ˢ univ ⊆ Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω)
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P)
    {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t ∈ parameterInterval, ∀ x, |M.scalarDerivative P x (Z t x)| ≤ D) :
    ∃ W : ℝ → (x : M.Point) → M.Tangent x,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun p : ℝ × M.Point => (⟨p.2, W p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) ∧
      (∀ t ∈ parameterInterval, W t = Z t) ∧
      ∀ t x, |M.scalarDerivative P x (W t x)| ≤ D + 2 := by
  obtain ⟨V, hV, heq⟩ := extend_strip_field Z hΩ hstrip hZ
  let χ : ContDiffBump (0 : ℝ) := ⟨D + 1, D + 2, by linarith, by linarith⟩
  let rate := fun p : ℝ × M.Point => M.scalarDerivative P p.2 (V p.1 p.2)
  let c := fun p : ℝ × M.Point => χ (rate p)
  have hc : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ c :=
    χ.contDiff.contMDiff.comp (smooth_scalar_rate V hV P hP)
  have hW := contMDiff_cutoff_field V isOpen_univ hV.contMDiffOn c hc (subset_univ _)
  refine ⟨fun t x => c (t,x) • V t x, hW, ?_, ?_⟩
  · intro t ht
    funext x
    have hrate : |rate (t,x)| ≤ D := by simpa only [rate, heq t ht] using hb t ht x
    have hone : c (t,x) = 1 := χ.one_of_mem_closedBall (by
      simpa only [χ, Metric.mem_closedBall, Real.dist_eq, sub_zero] using hrate.trans (by linarith : D ≤ D+1))
    simp only [hone, one_smul, heq t ht]
  · intro t x
    change |M.scalarDerivative P x (χ (rate (t,x)) • V t x)| ≤ D + 2
    simp only [scalarDerivative, map_smul, smul_eq_mul, abs_mul]
    change |χ (rate (t,x))| * |rate (t,x)| ≤ D + 2
    rw [abs_of_nonneg χ.nonneg]
    by_cases hr : |rate (t,x)| < D + 2
    · exact (mul_le_of_le_one_left (abs_nonneg _) χ.le_one).trans hr.le
    · have hz : χ (rate (t,x)) = 0 := χ.zero_of_le_dist (by
        simpa only [χ, Real.dist_eq, sub_zero] using le_of_not_gt hr)
      rw [hz, zero_mul]
      linarith
end ExactLiouvilleComparison.ODE
