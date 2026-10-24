import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAtlasCharts

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Atlas

variable {d : ℕ} (D : LiouvilleDomain d)

open scoped Classical in
def pretrivialization (x : D.domain.boundary.Point) :
    Pretrivialization (Model (d - 2)) (π (Model (d - 2)) (Fiber D)) where
  toFun p := (p.proj, coordinate D x p.proj p.snd)
  invFun p := if hp : p.1 ∈ chartDomain D x then
    ⟨p.1, (coordinateEquiv D x p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π (Model (d - 2)) (Fiber D)) ⁻¹' chartDomain D x
  target := chartDomain D x ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨y, v⟩
    change y ∈ chartDomain D x at hp
    dsimp only
    rw [dite_eq_left hp, ← coordinateEquiv_apply D x y hp]
    exact congrArg (fun w : Fiber D y ↦ (⟨y, w⟩ : TotalSpace (Model (d - 2)) (Fiber D)))
      ((coordinateEquiv D x y hp).symm_apply_apply v)
  right_inv' p hp := by
    rw [dite_eq_left hp.1, ← coordinateEquiv_apply D x p.1 hp.1]
    exact Prod.ext rfl ((coordinateEquiv D x p.1 hp.1).apply_symm_apply p.2)
  open_target := (chartDomain_open D x).prod isOpen_univ
  baseSet := chartDomain D x
  open_baseSet := chartDomain_open D x
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance pretrivialization_linear (x : D.domain.boundary.Point) :
    (pretrivialization D x).IsLinear ℝ where
  linear y _ := (coordinate D x y).isLinear

theorem pretrivialization_symm (x y : D.domain.boundary.Point)
    (hy : y ∈ chartDomain D x) (v : Model (d - 2)) :
    (pretrivialization D x).symm y v = (coordinateEquiv D x y hy).symm v := by
  apply (coordinateEquiv D x y hy).injective
  rw [(coordinateEquiv D x y hy).apply_symm_apply, coordinateEquiv_apply]
  exact congrArg Prod.snd ((pretrivialization D x).apply_mk_symm hy v)

theorem pretrivialization_isInducing (x y : D.domain.boundary.Point)
    (hy : y ∈ chartDomain D x) :
    Topology.IsInducing (pretrivialization D x ∘ TotalSpace.mk y) := by
  have h : Topology.IsInducing (coordinate D x y) := by
    convert (coordinateEquiv D x y hy).toHomeomorph.isInducing using 1
    funext v
    exact (coordinateEquiv_apply D x y hy v).symm
  exact Topology.IsInducing.of_comp
    (continuous_const.prodMk (coordinate D x y).continuous) continuous_snd h

def transition (x x' y : D.domain.boundary.Point) : Model (d - 2) →L[ℝ] Model (d - 2) :=
  (fixedProjection D x').comp
    (((ambientChart D x).coordChangeL ℝ (ambientChart D x') y).toContinuousLinearMap.comp
      (reconstruction D x y))

theorem transition_smooth (x x' : D.domain.boundary.Point) :
    ContMDiffOn 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 2)) ∞
      (transition D x x') (chartDomain D x ∩ chartDomain D x') := by
  have h := (contMDiffOn_coordChangeL (IB := 𝓘(ℝ, Model (d - 1)))
    (n := ∞) (ambientChart D x) (ambientChart D x')).mono
      (t := chartDomain D x ∩ chartDomain D x') (fun _ hy ↦ ⟨hy.1.1, hy.2.1⟩)
  exact contMDiffOn_const.clm_comp
    (h.clm_comp ((reconstruction_smooth D x).mono inter_subset_left))

theorem transition_apply (x x' y : D.domain.boundary.Point)
    (hy : y ∈ chartDomain D x ∩ chartDomain D x') (v : Model (d - 2)) :
    transition D x x' y v =
      (pretrivialization D x' ⟨y, (pretrivialization D x).symm y v⟩).2 := by
  rw [pretrivialization_symm D x y hy.1]
  change fixedProjection D x' ((ambientChart D x).coordChangeL ℝ (ambientChart D x') y
      (reconstruction D x y v)) =
    fixedProjection D x' ((ambientChart D x').continuousLinearMapAt ℝ y
      ((coordinateEquiv D x y hy.1).symm v : D.domain.boundary.Tangent y))
  rw [coordinateEquiv_symm_ambient, Trivialization.coordChangeL_apply _ _ ⟨hy.1.1, hy.2.1⟩,
    Trivialization.continuousLinearMapAt_apply_of_mem _ _ hy.2.1,
    Trivialization.symmL_apply _ hy.1.1]

/-- Actual native local charts of the literal boundary primitive kernel. -/
def prebundle : Prebundle D where
  pretrivializationAtlas := range (pretrivialization D)
  pretrivialization_linear' := by rintro _ ⟨x, rfl⟩; infer_instance
  pretrivializationAt := pretrivialization D
  mem_base_pretrivializationAt := mem_chartDomain D
  pretrivialization_mem_atlas x := ⟨x, rfl⟩
  exists_coordChange := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
    exact ⟨transition D x x', (transition_smooth D x x').continuousOn,
      fun y hy v ↦ transition_apply D x x' y hy v⟩
  totalSpaceMk_isInducing x := pretrivialization_isInducing D x x (mem_chartDomain D x)

instance prebundle_isContMDiff : (prebundle D).IsContMDiff 𝓘(ℝ, Model (d - 1)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
    exact ⟨transition D x x', transition_smooth D x x',
      fun y hy v ↦ transition_apply D x x' y hy v⟩

theorem prebundle_smooth :
    let P := prebundle D
    letI := P.totalSpaceTopology
    letI := P.toFiberBundle
    letI := P.toVectorBundle
    ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) :=
  (prebundle D).contMDiffVectorBundle 𝓘(ℝ, Model (d - 1))

theorem reconstruction_coordinate (x y : D.domain.boundary.Point)
    (hy : y ∈ chartDomain D x) (v : Fiber D y) :
    reconstruction D x y (coordinate D x y v) =
      (ambientChart D x).continuousLinearMapAt ℝ y (v : D.domain.boundary.Tangent y) := by
  have h := congrArg (fun w : Fiber D y ↦
    (ambientChart D x).continuousLinearMapAt ℝ y (w : D.domain.boundary.Tangent y))
    ((coordinateEquiv D x y hy).symm_apply_apply v)
  rw [coordinateEquiv_symm_ambient, Trivialization.continuousLinearMapAt_symmL _ hy.1,
    coordinateEquiv_apply] at h
  exact h

section Native

local instance : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) :=
  (prebundle D).totalSpaceTopology
local instance : FiberBundle (Model (d - 2)) (Fiber D) := (prebundle D).toFiberBundle
local instance : VectorBundle ℝ (Model (d - 2)) (Fiber D) := (prebundle D).toVectorBundle
local instance : ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) :=
  prebundle_smooth D

theorem native_symmL (x y : D.domain.boundary.Point) (hy : y ∈ chartDomain D x)
    (v : Model (d - 2)) :
    (trivializationAt (Model (d - 2)) (Fiber D) x).symmL ℝ y v =
      (coordinateEquiv D x y hy).symm v := by
  rw [Trivialization.symmL_apply _ hy]
  exact pretrivialization_symm D x y hy v

theorem inclusion_coordinates (x y : D.domain.boundary.Point) (hy : y ∈ chartDomain D x) :
    ContinuousLinearMap.inCoordinates (Model (d - 2)) (Fiber D)
      (Model (d - 1)) D.domain.boundary.Tangent x y x y
      (D.domain.boundary.contactHyperplane (boundaryAlpha D) y).subtypeL =
        reconstruction D x y := by
  ext v : 1
  change (ambientChart D x).continuousLinearMapAt ℝ y
    ((trivializationAt (Model (d - 2)) (Fiber D) x).symmL ℝ y v :
      D.domain.boundary.Tangent y) = _
  rw [native_symmL D x y hy, coordinateEquiv_symm_ambient,
    Trivialization.continuousLinearMapAt_symmL _ hy.1]

theorem inclusion_smooth :
    ContMDiff 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod
        𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 1))) ∞
      (fun y ↦ TotalSpace.mk' (Model (d - 2) →L[ℝ] Model (d - 1)) y
        (D.domain.boundary.contactHyperplane (boundaryAlpha D) y).subtypeL) := by
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  apply ((reconstruction_smooth D x).contMDiffAt
    ((chartDomain_open D x).mem_nhds (mem_chartDomain D x))).congr_of_eventuallyEq
  filter_upwards [(chartDomain_open D x).mem_nhds (mem_chartDomain D x)] with y hy
  exact inclusion_coordinates D x y hy

theorem smooth_restriction_iff (n : ℕ) (N : SmoothManifold n)
    (f : N.Point → D.domain.boundary.Point) (s : (z : N.Point) → Fiber D (f z)) :
    ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 2))) ∞
      (fun z ↦ TotalSpace.mk' (Model (d - 2)) (f z) (s z)) ↔
    ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 1))) ∞
      (fun z ↦ TotalSpace.mk' (Model (d - 1)) (f z)
        (s z : D.domain.boundary.Tangent (f z))) := by
  constructor
  · intro hs z
    obtain ⟨hf, hv⟩ := Bundle.contMDiffAt_totalSpace.mp (hs z)
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hf, ?_⟩
    change ContMDiffAt 𝓘(ℝ, Model n) 𝓘(ℝ, Model (d - 2)) ∞
      (fun w ↦ coordinate D (f z) (f w) (s w)) z at hv
    have hr := ((reconstruction_smooth D (f z)).contMDiffAt
      ((chartDomain_open D (f z)).mem_nhds (mem_chartDomain D (f z)))).comp z hf
    apply (hr.clm_apply hv).congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      ((chartDomain_open D (f z)).mem_nhds (mem_chartDomain D (f z)))] with w hw
    change (ambientChart D (f z) ⟨f w, (s w : D.domain.boundary.Tangent (f w))⟩).2 = _
    dsimp only [Function.comp_def]
    rw [reconstruction_coordinate D (f z) (f w) hw,
      Trivialization.continuousLinearMapAt_apply_of_mem _ _ hw.1]
  · intro hs z
    obtain ⟨hf, hv⟩ := Bundle.contMDiffAt_totalSpace.mp (hs z)
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hf, ?_⟩
    apply ((fixedProjection D (f z)).contMDiff.contMDiffAt.comp z hv).congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      ((chartDomain_open D (f z)).mem_nhds (mem_chartDomain D (f z)))] with w hw
    change coordinate D (f z) (f w) (s w) =
      fixedProjection D (f z) (ambientChart D (f z)
        ⟨f w, (s w : D.domain.boundary.Tangent (f w))⟩).2
    simp only [coordinate, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Trivialization.continuousLinearMapAt_apply_of_mem _ _ hw.1]

end Native

theorem atlasProperties : AtlasProperties D (prebundle D) :=
  ⟨prebundle_smooth D, inclusion_smooth D, smooth_restriction_iff D⟩

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Atlas

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle

/-- The commissioned unconditional native kernel-atlas construction. -/
theorem atlas_exists (d : ℕ) (D : LiouvilleDomain d) :
    ∃ P : Prebundle D, AtlasProperties D P :=
  ⟨Atlas.prebundle D, Atlas.atlasProperties D⟩

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle
