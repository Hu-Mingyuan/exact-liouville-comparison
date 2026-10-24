import FsFltz.Geometry.FamilyLiouvilleLocalFlow

/-! Bounded smooth cutoffs and native tangent-section extension for ODE continuation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Function FsFltz.Geometry

namespace ExactLiouvilleComparison.ODE

section Cutoff
variable {E H Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [FiniteDimensional ℝ E] [LocallyCompactSpace H]
  [T2Space Q] [SecondCountableTopology Q]

/-- Retain the range bound in the native smooth cutoff construction.
The bound is needed to preserve the scalar estimate after multiplying a field. -/
theorem exists_bounded_smooth_compact_cutoff
    {K U : Set Q} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : Q → ℝ) (V : TopologicalSpace.Opens Q),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧
      K ⊆ (V : Set Q) ∧ (∀ p ∈ V, χ p = 1) ∧
      IsCompact (tsupport χ) ∧ tsupport χ ⊆ U := by
  let := ChartedSpace.locallyCompactSpace H Q
  obtain ⟨B, hBo, hKB, hBc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨S, hSo, hKS, hSc⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hBo).mem_nhdsSet.mpr (subset_inter hKU hKB))
  obtain ⟨V, hVo, hKV, hVc⟩ := hK.exists_isOpen_closure_subset (hSo.mem_nhdsSet.mpr hKS)
  obtain ⟨χ, hχ, hχrange, hχS, hχV⟩ := exists_contMDiff_support_eq_eq_one_iff I
    (n := ⊤) hSo isClosed_closure hVc
  have hcc : IsCompact (closure S) := hBc.of_isClosed_subset isClosed_closure
    (hSc.trans (inter_subset_right.trans subset_closure))
  refine ⟨χ, ⟨V, hVo⟩, hχ, fun p => hχrange (mem_range_self p), hKV, ?_, ?_, ?_⟩
  · intro p hp
    exact (hχV p).mp (subset_closure hp)
  · simpa only [tsupport, hχS] using hcc
  · simpa only [tsupport, hχS] using hSc.trans inter_subset_left
end Cutoff

variable {d : ℕ} {M : SmoothManifold d}

/-- Cutting off a native real-time tangent field inside its open smooth domain
produces a globally smooth native section. The product-bundle bridge is explicit. -/
theorem contMDiff_cutoff_field
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    {Ω : Set (ℝ × M.Point)} (hΩ : IsOpen Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω)
    (χ : ℝ × M.Point → ℝ)
    (hχ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ Ω) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, χ p • Z p.1 p.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) M.Point)) := by
  let v : (p : ℝ × M.Point) → TangentSpace ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) p :=
    fun p => (0, Z p.1 p.2)
  have hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)).tangent) ∞
      (fun p => (⟨p, v p⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (ℝ × M.Point))) Ω := by
    have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
        (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
      ((ht.comp contMDiff_fst).contMDiffOn.prodMk hZ)
  exact (contMDiff_equivTangentBundleProd.comp
    (hχ.contMDiffOn.smul_section_of_tsupport hΩ hsupp hv)).snd

end ExactLiouvilleComparison.ODE
