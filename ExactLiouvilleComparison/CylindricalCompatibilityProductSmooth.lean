import ExactLiouvilleComparison.CylindricalCompatibilityEndAlgebra
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Native product tangent coordinates for the prescribed cylindrical operator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Bundle Set Filter ContinuousLinearMap

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {b : ℕ} (M : SmoothManifold b)

lemma product_tangent_coordinates (a x : M.Point × ℝ)
    (hx : x.1 ∈ (chartAt (Model b) a.1).source) :
    (trivializationAt (Model b × ℝ)
      (TangentSpace ((𝓘(ℝ, Model b)).prod 𝓘(ℝ, ℝ))) a).continuousLinearMapAt ℝ x =
    ((trivializationAt (Model b) M.Tangent a.1).continuousLinearMapAt ℝ x.1).prodMap
      (ContinuousLinearMap.id ℝ ℝ) := by
  have hxp : x ∈ (chartAt (ModelProd (Model b) ℝ) a).source := by simpa only [mfld_simps] using hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hxp,
    TangentBundle.continuousLinearMapAt_trivializationAt hx]
  have h := mfderiv_prodMap (I := 𝓘(ℝ, Model b)) (I' := 𝓘(ℝ, ℝ))
    (J := 𝓘(ℝ, Model b)) (J' := 𝓘(ℝ, ℝ))
    (((contMDiffOn_chart (I := 𝓘(ℝ, Model b)) (n := ∞) (x := a.1)).contMDiffAt
      ((chartAt (Model b) a.1).open_source.mem_nhds hx)).mdifferentiableAt (by simp)) (mdifferentiableAt_id (x := x.2))
  simp +instances only [mfld_simps, mfderiv_id, Function.comp_def,
    OpenPartialHomeomorph.prod_toPartialHomeomorph, PartialEquiv.prod_coe] at *
  convert h using 1 <;> congr 1
  · exact modelWithCornersSelf_prod
  · exact chartedSpaceSelf_prod.symm

lemma product_tangent_inverse_coordinates (a x : M.Point × ℝ)
    (hx : x.1 ∈ (chartAt (Model b) a.1).source) :
    (trivializationAt (Model b × ℝ)
      (TangentSpace ((𝓘(ℝ, Model b)).prod 𝓘(ℝ, ℝ))) a).symmL ℝ x =
    ((trivializationAt (Model b) M.Tangent a.1).symmL ℝ x.1).prodMap
      (ContinuousLinearMap.id ℝ ℝ) := by
  have hxp : x ∈ (chartAt (ModelProd (Model b) ℝ) a).source := by simpa only [mfld_simps] using hx
  rw [TangentBundle.symmL_trivializationAt hxp, TangentBundle.symmL_trivializationAt hx]
  have hy := (chartAt (Model b) a.1).map_source hx
  have h := mfderiv_prodMap (I := 𝓘(ℝ, Model b)) (I' := 𝓘(ℝ, ℝ))
    (J := 𝓘(ℝ, Model b)) (J' := 𝓘(ℝ, ℝ))
    (f := (chartAt (Model b) a.1).symm) (g := (id : ℝ → ℝ))
    (p := (chartAt (Model b) a.1 x.1, x.2))
    (((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model b)) (n := ∞) (x := a.1)).contMDiffAt
      ((chartAt (Model b) a.1).open_target.mem_nhds hy)).mdifferentiableAt (by simp))
    (mdifferentiableAt_id (x := x.2))
  simp +instances only [mfld_simps, mfderiv_id, mfderivWithin_univ,
    Function.comp_def, OpenPartialHomeomorph.prod_toPartialHomeomorph,
    PartialEquiv.prod_coe, PartialEquiv.refl_symm, Prod.map_id, range_id] at *
  convert h using 1 <;> congr 1
  · exact modelWithCornersSelf_prod
  · exact chartedSpaceSelf_prod.symm

variable {d : ℕ} {D : LiouvilleDomain d}

/-- The full product formula is a smooth section of the native tangent Hom bundle. -/
theorem ContactData.smooth_endJ (P : ContactData D) :
    ContMDiff ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ))
      (((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ)).prod
        𝓘(ℝ, (Model (d-1) × ℝ) →L[ℝ] (Model (d-1) × ℝ))) ∞
      (fun q : D.domain.boundary.Point × ℝ => TotalSpace.mk'
        ((Model (d-1) × ℝ) →L[ℝ] (Model (d-1) × ℝ))
        (E := fun z : D.domain.boundary.Point × ℝ => TangentSpace ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ)) z →L[ℝ]
          TangentSpace ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ)) z) q (P.endJ q.1)) := by
  intro a
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let N := D.domain.boundary
  let c := chartAt (Model (d-1)) a.1
  let e := trivializationAt (Model (d-1)) N.Tangent a.1
  have ha : a.1 ∈ c.source := mem_chart_source _ _
  have ht := c.map_source ha
  have hfst : ContMDiffAt ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model (d-1)) ∞ (Prod.fst : D.domain.boundary.Point × ℝ → _) a :=
    contMDiffAt_fst
  have hc : ContMDiffAt ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model (d-1)) ∞ (fun q : D.domain.boundary.Point × ℝ => c q.1) a :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, Model (d-1)))
    (n := ∞) (x := a.1)).contMDiffAt (c.open_source.mem_nhds ha)).comp a hfst
  have hR := ((P.smooth_reeb a.1).contDiffAt
    (c.open_target.mem_nhds ht)).contMDiffAt.comp a hc
  have hsAlpha : N.IsSmoothForm (alpha D) :=
    N.isSmoothForm_pullback_one D.domain.extension D.domain.boundaryInclusion.map
      D.liouville.primitive D.liouville.smooth_primitive
  have hAlpha := ((hsAlpha a.1).contDiffAt
    (c.open_target.mem_nhds ht)).contMDiffAt.comp a hc
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model (d-1)) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.symm
  have hA := L.contDiff.contMDiff.contMDiffAt.comp a hAlpha
  have hK := (((contMDiffAt_hom_bundle _).mp (P.smooth_J a.1)).2).comp a hfst
  let f : (Model (d-1) × ℝ) →L[ℝ] Model (d-1) := ContinuousLinearMap.fst ℝ _ _
  let s : (Model (d-1) × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ _ _
  let l : Model (d-1) →L[ℝ] (Model (d-1) × ℝ) := ContinuousLinearMap.inl ℝ _ _
  let r : ℝ →L[ℝ] (Model (d-1) × ℝ) := ContinuousLinearMap.inr ℝ _ _
  have hf : ContMDiffAt ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Model (d-1) × ℝ) →L[ℝ] Model (d-1)) ∞ (fun _ => f) a := contMDiffAt_const
  have hl : ContMDiffAt ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model (d-1) →L[ℝ] (Model (d-1) × ℝ)) ∞ (fun _ => l) a := contMDiffAt_const
  have hr : ContMDiffAt ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, ℝ →L[ℝ] (Model (d-1) × ℝ)) ∞ (fun _ => r) a := contMDiffAt_const
  have hRank := (ContinuousLinearMap.smulRightL ℝ (Model (d-1) × ℝ)
    (Model (d-1)) s).contMDiff.contMDiffAt.comp a hR
  apply ((hl.clm_comp ((hK.clm_comp hf).add hRank)).add
    (hr.clm_comp (hA.clm_comp hf).neg)).congr_of_eventuallyEq
  have hU : ∀ᶠ q : D.domain.boundary.Point × ℝ in 𝓝 a, q.1 ∈ c.source :=
    continuous_fst.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds ha)
  filter_upwards [hU] with q hq
  simp only [Function.comp_apply]
  rw [inCoordinates, product_tangent_coordinates N a q hq,
    product_tangent_inverse_coordinates N a q hq]
  apply ContinuousLinearMap.ext
  intro z
  rcases z with ⟨v,t⟩
  change ((e.continuousLinearMapAt ℝ q.1)
      (P.J q.1 (e.symmL ℝ q.1 v) + t • P.reeb q.1),
      -evalOne (alpha D) q.1 (e.symmL ℝ q.1 v)) = _
  rw [map_add, map_smul]
  simp only [Pi.add_apply, Function.comp_apply, l, r, f, s,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.comp_apply, add_apply,
    neg_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', Prod.mk_add_mk, add_zero, zero_add]
  congr 1
  · rw [inCoordinates]
    dsimp only [vectorInChart]
    rw [c.left_inv hq, TangentBundle.continuousLinearMapAt_trivializationAt hq]
    rfl
  · dsimp only [L, formInChart]
    rw [c.left_inv hq, TangentBundle.symmL_trivializationAt hq]
    simp only [mfld_simps, mfderivWithin_univ]
    rfl

end ExactLiouvilleComparison.CylindricalCompatibility
