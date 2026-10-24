import ExactLiouvilleComparison.MoserExactnessStatement
import FsFltz.Geometry.CompletionFamily

/-! Smooth scalar contraction along the native Moser evolution. -/
noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

set_option backward.isDefEq.respectTransparency false in
/-- Pairing a form and vector in a fixed chart is the intrinsic pairing. -/
theorem chart_pairing (alpha : M.Form 1) (Z : (x : M.Point) → M.Tangent x)
    (a : M.Point) {y : Model d} (hy : y ∈ (chartAt (Model d) a).target) :
    M.formInChart a alpha y (fun _ => M.vectorInChart a Z y) =
      evalOne alpha ((chartAt (Model d) a).symm y) (Z ((chartAt (Model d) a).symm y)) := by
  let c := chartAt (Model d) a
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv
    (c.map_target hy)
  have he := congrArg (fun L => L (Z (c.symm y))) hinv
  rw [c.right_inv hy] at he
  change alpha (c.symm y) (fun _ =>
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm y)
      ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c (c.symm y)) (Z (c.symm y)))) = _
  change _ = Z (c.symm y) at he
  apply congrArg (alpha (c.symm y))
  funext i
  exact he

/-- Smooth real extensions of a one-form and field have a smooth scalar pairing. -/
theorem isSmoothScalarFamily_pairing (mu : ℝ → M.Form 1)
    (hmu : M.IsSmoothFormFamily mu)
    (Z : (t : ℝ) → (x : M.Point) → M.Tangent x)
    (hZ : M.IsSmoothVectorFieldFamily Z) :
    M.IsSmoothScalarFamily (fun t x => evalOne (mu t) x (Z t x)) := by
  intro a
  obtain ⟨U, hU, hUc, hmuU⟩ := hmu a
  obtain ⟨V, hV, hVc, hZV⟩ := hZ a
  let W := (U ∩ V) ∩ (univ ×ˢ (chartAt (Model d) a).target)
  have hW : IsOpen W := (hU.inter hV).inter
    (isOpen_univ.prod (chartAt (Model d) a).open_target)
  refine ⟨W, hW, fun p hp => ⟨⟨hUc hp, hVc hp⟩, mem_univ _, hp.2⟩, ?_⟩
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := (e.symm.contDiff.comp_contDiffOn (hmuU.mono
    (show W ⊆ U from fun _ h => h.1.1))).clm_apply
    (hZV.mono (show W ⊆ V from fun _ h => h.1.2))
  apply hs.congr
  intro p hp
  exact (chart_pairing (mu p.1) (Z p.1) a hp.2.2).symm

set_option backward.isDefEq.respectTransparency false in
/-- Scalar composition preserves genuine open interval extensions. -/
theorem isSmoothScalarFamily_comp (f : ℝ → M.Point → M.Point)
    (hf : M.IsSmoothMapFamily M f) (q : ℝ → M.Point → ℝ)
    (hq : M.IsSmoothScalarFamily q) :
    M.IsSmoothScalarFamily (fun t x => q t (f t x)) := by
  obtain ⟨R, hR, hRc, hfR⟩ := hf
  intro a
  apply smoothNearInterval_of_local
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  let c := chartAt (Model d) a
  let b := chartAt (Model d) (f t (c.symm y))
  let q₀ : ℝ × Model d → ℝ × M.Point := fun p => (p.1, c.symm p.2)
  have hq₀ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ q₀ (univ ×ˢ c.target) :=
    contMDiffOn_fst.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).comp
        contMDiffOn_snd (fun _ hp => hp.2))
  let W := (univ ×ˢ c.target) ∩ q₀ ⁻¹' R
  have hW : IsOpen W := hq₀.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) hR
  let k : ℝ × Model d → M.Point := fun p => f p.1 (c.symm p.2)
  have hk : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ k W :=
    hfR.comp (hq₀.mono inter_subset_left) inter_subset_right
  let S := W ∩ k ⁻¹' b.source
  have hS : IsOpen S := hk.continuousOn.isOpen_inter_preimage hW b.open_source
  have hpS : (t, y) ∈ S :=
    ⟨⟨⟨mem_univ _, hy⟩, hRc ⟨ht, mem_univ _⟩⟩, mem_chart_source _ _⟩
  let g : ℝ × Model d → Model d := fun p => b (k p)
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ g S :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := f t (c.symm y))).comp
      (hk.mono inter_subset_left) inter_subset_right
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g S := hgm.contDiffOn
  obtain ⟨A, hA, hAc, hqA⟩ := hq (f t (c.symm y))
  let r : ℝ × Model d → ℝ × Model d := fun p => (p.1, g p)
  have hr : ContDiffOn ℝ ∞ r S := contDiffOn_fst.prodMk hg
  let U := S ∩ r ⁻¹' A
  have hU : IsOpen U := hr.continuousOn.isOpen_inter_preimage hS hA
  have hpU : (t, y) ∈ U :=
    ⟨hpS, hAc ⟨ht, b.map_source (mem_chart_source _ _)⟩⟩
  have hs := hqA.comp (hr.mono inter_subset_left) inter_subset_right
  refine ⟨U, hU, hpU, hs.congr ?_⟩
  intro p hp
  change q p.1 (k p) = q p.1 (b.symm (b (k p)))
  rw [b.left_inv hp.1.2]

/-- Fixing the initial time of an evolution retains its open smooth extension. -/
theorem evolution_isSmoothMapFamily {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) (s : Parameter) :
    M.IsSmoothMapFamily M (E.extension s.val) := by
  obtain ⟨U, hU, hUc, hE⟩ := E.smooth
  let j : ℝ × M.Point → ℝ × (ℝ × M.Point) := fun p => (s.val, p)
  have hj : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞ j :=
    contMDiff_const.prodMk contMDiff_id
  refine ⟨j ⁻¹' U, hU.preimage hj.continuous, ?_, ?_⟩
  · intro p hp
    exact hUc ⟨s.property, hp⟩
  · exact hE.comp hj.contMDiffOn (fun _ hp => hp)

/-- The literal contraction along the evolution has a genuine smooth extension,
including at both endpoints. No equation for a pulled-back form is assumed. -/
theorem contractionAlong_isSmoothIntervalScalarFamily
    (mu : ℝ → M.Form 1) (hmu : M.IsSmoothFormFamily mu)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) (E : FirstPathFlow.Evolution Z) :
    M.IsSmoothIntervalScalarFamily (contractionAlong mu E) := by
  obtain ⟨Z', hZ', heq⟩ := hZ
  refine ⟨fun t x => evalOne (mu t) (E.extension 0 t x) (Z' t (E.extension 0 t x)),
    isSmoothScalarFamily_comp (E.extension 0) (evolution_isSmoothMapFamily E parameterZero)
      _ (isSmoothScalarFamily_pairing mu hmu Z' hZ'), ?_⟩
  intro t
  funext x
  change evalOne (mu t.val) (E.extension parameterZero.val t.val x)
    (Z' t.val (E.extension parameterZero.val t.val x)) = _
  rw [E.agrees parameterZero t, heq t]
  rfl
end ExactLiouvilleComparison.MoserExactness
