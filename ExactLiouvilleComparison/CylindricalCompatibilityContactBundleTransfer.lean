import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAtlas
import FsFltz.Geometry.VectorFieldBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Transfer

section Composition
variable {n k₁ k₂ k₃ : ℕ} (M : SmoothManifold n)
  (E₁ E₂ E₃ : M.Point → Type*)
  [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul ℝ (E₁ x)]
  [∀ x, TopologicalSpace (E₂ x)] [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul ℝ (E₂ x)]
  [∀ x, TopologicalSpace (E₃ x)] [∀ x, AddCommGroup (E₃ x)] [∀ x, Module ℝ (E₃ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul ℝ (E₃ x)]
  [TopologicalSpace (TotalSpace (Model k₁) E₁)] [FiberBundle (Model k₁) E₁]
  [VectorBundle ℝ (Model k₁) E₁] [ContMDiffVectorBundle ∞ (Model k₁) E₁ 𝓘(ℝ, Model n)]
  [TopologicalSpace (TotalSpace (Model k₂) E₂)] [FiberBundle (Model k₂) E₂]
  [VectorBundle ℝ (Model k₂) E₂] [ContMDiffVectorBundle ∞ (Model k₂) E₂ 𝓘(ℝ, Model n)]
  [TopologicalSpace (TotalSpace (Model k₃) E₃)] [FiberBundle (Model k₃) E₃]
  [VectorBundle ℝ (Model k₃) E₃] [ContMDiffVectorBundle ∞ (Model k₃) E₃ 𝓘(ℝ, Model n)]

/-- Native composition, proved by cancellation in actual bundle coordinates. -/
theorem hom_comp_smooth
    (A : (x : M.Point) → E₁ x →L[ℝ] E₂ x)
    (B : (x : M.Point) → E₂ x →L[ℝ] E₃ x)
    (hA : ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model n)).prod 𝓘(ℝ, Model k₁ →L[ℝ] Model k₂)) ∞
      (fun x ↦ TotalSpace.mk' (Model k₁ →L[ℝ] Model k₂) x (A x)))
    (hB : ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model n)).prod 𝓘(ℝ, Model k₂ →L[ℝ] Model k₃)) ∞
      (fun x ↦ TotalSpace.mk' (Model k₂ →L[ℝ] Model k₃) x (B x))) :
    ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model n)).prod 𝓘(ℝ, Model k₁ →L[ℝ] Model k₃)) ∞
      (fun x ↦ TotalSpace.mk' (Model k₁ →L[ℝ] Model k₃) x ((B x).comp (A x))) := by
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  have ha := ((contMDiffAt_hom_bundle _).mp (hA x)).2
  have hb := ((contMDiffAt_hom_bundle _).mp (hB x)).2
  apply (hb.clm_comp ha).congr_of_eventuallyEq
  filter_upwards [(trivializationAt (Model k₂) E₂ x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x)] with y hy
  ext v : 1
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt _ hy]

end Composition

variable {d : ℕ} (D : LiouvilleDomain d)

section Native
local instance : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) :=
  (Atlas.prebundle D).totalSpaceTopology
local instance : FiberBundle (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toFiberBundle
local instance : VectorBundle ℝ (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toVectorBundle
local instance : ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) :=
  Atlas.prebundle_smooth D

theorem native_coordinate (x y : D.domain.boundary.Point)
    (hy : y ∈ Atlas.chartDomain D x) (v : Fiber D y) :
    (trivializationAt (Model (d - 2)) (Fiber D) x).continuousLinearMapAt ℝ y v =
      Atlas.coordinate D x y v := by
  rw [Trivialization.continuousLinearMapAt_apply_of_mem _ _ hy]
  rfl

section Restriction
variable {k : ℕ} (E : D.domain.boundary.Point → Type*)
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]
  [TopologicalSpace (TotalSpace (Model k) E)] [FiberBundle (Model k) E]
  [VectorBundle ℝ (Model k) E]
  [ContMDiffVectorBundle ∞ (Model k) E 𝓘(ℝ, Model (d - 1))]

/-- Codomain restriction of a native smooth bundle map to the actual kernel. -/
theorem intoKernel_smooth
    (A : (y : D.domain.boundary.Point) → E y →L[ℝ] D.domain.boundary.Tangent y)
    (p : (y : D.domain.boundary.Point) → E y →L[ℝ] Fiber D y)
    (hp : ∀ y v, (p y v : D.domain.boundary.Tangent y) = A y v)
    (hA : ContMDiff 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model k →L[ℝ] Model (d - 1))) ∞
      (fun y ↦ TotalSpace.mk' (Model k →L[ℝ] Model (d - 1)) y (A y))) :
    ContMDiff 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model k →L[ℝ] Model (d - 2))) ∞
      (fun y ↦ TotalSpace.mk' (Model k →L[ℝ] Model (d - 2)) y (p y)) := by
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  have ha := ((contMDiffAt_hom_bundle _).mp (hA x)).2
  apply ((contMDiffAt_const (c := Atlas.fixedProjection D x)).clm_comp ha).congr_of_eventuallyEq
  filter_upwards [(Atlas.chartDomain_open D x).mem_nhds (Atlas.mem_chartDomain D x)] with y hy
  ext v : 1
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [native_coordinate D x y hy]
  change Atlas.fixedProjection D x ((Atlas.ambientChart D x).continuousLinearMapAt ℝ y
    (p y ((trivializationAt (Model k) E x).symmL ℝ y v) : D.domain.boundary.Tangent y)) = _
  rw [hp]

end Restriction

theorem restriction_smooth
    (A : (y : D.domain.boundary.Point) →
      D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y)
    (hA : SmoothEndomorphism D.domain.boundary A)
    (hpres : ∀ y v, v ∈ D.domain.boundary.contactHyperplane (boundaryAlpha D) y →
      A y v ∈ D.domain.boundary.contactHyperplane (boundaryAlpha D) y) :
    SmoothKernelEndomorphism D (Atlas.prebundle D) (fun y ↦ (A y).restrict (hpres y)) := by
  apply intoKernel_smooth D (Fiber D)
    (fun y ↦ (A y).comp (D.domain.boundary.contactHyperplane (boundaryAlpha D) y).subtypeL)
    (fun y ↦ (A y).restrict (hpres y)) (fun _ _ ↦ rfl)
  exact hom_comp_smooth D.domain.boundary (Fiber D) D.domain.boundary.Tangent
    D.domain.boundary.Tangent _ _ (Atlas.inclusion_smooth D) hA

def ambientProjection (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (y : D.domain.boundary.Point) : D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y :=
  ContinuousLinearMap.id ℝ _ - (Atlas.covector D y).smulRight (R y)

theorem ambientProjection_apply
    (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (y : D.domain.boundary.Point) (v : D.domain.boundary.Tangent y) :
    ambientProjection D R y v = v - evalOne (boundaryAlpha D) y v • R y := rfl

theorem ambientProjection_smooth
    (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (hR : D.domain.boundary.IsSmoothVectorField R) :
    SmoothEndomorphism D.domain.boundary (ambientProjection D R) := by
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  let e := Atlas.ambientChart D x
  have hr := ((Bundle.contMDiffAt_section x).mp (hR.contMDiff_section x))
  have ha := (Atlas.coefficient_smooth D x).contMDiffAt
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x))
  have hspan := (ContinuousLinearMap.toSpanSingletonLIE ℝ (Model (d - 1))).toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt.comp x hr
  have hs : ContMDiffAt 𝓘(ℝ, Model (d - 1))
      𝓘(ℝ, Model (d - 1) →L[ℝ] Model (d - 1)) ∞
      (fun y ↦ ContinuousLinearMap.id ℝ (Model (d - 1)) -
        (Atlas.coefficient D x y).smulRight (e ⟨y, R y⟩).2) x :=
    contMDiffAt_const.sub (hspan.clm_comp ha)
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x)] with y hy
  ext v : 1
  change e.continuousLinearMapAt ℝ y
    ((e.symmL ℝ y v) - Atlas.covector D y (e.symmL ℝ y v) • R y) =
      v - Atlas.coefficient D x y v • (e ⟨y, R y⟩).2
  rw [map_sub, map_smul, e.continuousLinearMapAt_symmL hy,
    e.continuousLinearMapAt_apply_of_mem ℝ hy]
  rfl

/-- Actual normalized projection to the literal kernel. The Reeb equation is
not needed for its smoothness; the full consumer retains that supplied premise. -/
def projection
    (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (hn : ∀ y, evalOne (boundaryAlpha D) y (R y) = 1)
    (y : D.domain.boundary.Point) : D.domain.boundary.Tangent y →L[ℝ] Fiber D y :=
  (ambientProjection D R y).codRestrict
    (D.domain.boundary.contactHyperplane (boundaryAlpha D) y) (fun v ↦ by
      change Atlas.covector D y (v - Atlas.covector D y v • R y) = 0
      have h : Atlas.covector D y (R y) = 1 := hn y
      simp [map_sub, map_smul, h])

theorem projection_self
    (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (hn : ∀ y, evalOne (boundaryAlpha D) y (R y) = 1)
    (y : D.domain.boundary.Point) : projection D R hn y (R y) = 0 := by
  apply Subtype.ext
  change R y - evalOne (boundaryAlpha D) y (R y) • R y = 0
  rw [hn, one_smul, sub_self]

theorem projection_subtype
    (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (hn : ∀ y, evalOne (boundaryAlpha D) y (R y) = 1)
    (y : D.domain.boundary.Point) (v : Fiber D y) : projection D R hn y v = v := by
  apply Subtype.ext
  have hv : Atlas.covector D y v = 0 := v.property
  change (v : D.domain.boundary.Tangent y) - Atlas.covector D y v • R y = v
  rw [hv, zero_smul, sub_zero]

theorem projection_smooth
    (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (hn : ∀ y, evalOne (boundaryAlpha D) y (R y) = 1)
    (hR : D.domain.boundary.IsSmoothVectorField R) :
    ContMDiff 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 1) →L[ℝ] Model (d - 2))) ∞
      (fun y ↦ TotalSpace.mk' (Model (d - 1) →L[ℝ] Model (d - 2)) y (projection D R hn y)) :=
  intoKernel_smooth D D.domain.boundary.Tangent (ambientProjection D R)
    (projection D R hn) (fun _ _ ↦ rfl) (ambientProjection_smooth D R hR)

theorem zeroExtension_smooth
    (p : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y →L[ℝ] Fiber D y)
    (hp : ContMDiff 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 1) →L[ℝ] Model (d - 2))) ∞
      (fun y ↦ TotalSpace.mk' (Model (d - 1) →L[ℝ] Model (d - 2)) y (p y)))
    (j : (y : D.domain.boundary.Point) → Fiber D y →L[ℝ] Fiber D y)
    (hj : SmoothKernelEndomorphism D (Atlas.prebundle D) j) :
    SmoothEndomorphism D.domain.boundary
      (fun y ↦ (D.domain.boundary.contactHyperplane (boundaryAlpha D) y).subtypeL.comp
        ((j y).comp (p y))) :=
  hom_comp_smooth D.domain.boundary D.domain.boundary.Tangent (Fiber D)
    D.domain.boundary.Tangent _ _
    (hom_comp_smooth D.domain.boundary D.domain.boundary.Tangent (Fiber D) (Fiber D)
      p j hp hj) (Atlas.inclusion_smooth D)

end Native

theorem transferProperties : TransferProperties D (Atlas.prebundle D) := by
  constructor
  · intro A hA hpres
    exact ⟨(fun y ↦ (A y).restrict (hpres y)), restriction_smooth D A hA hpres,
      fun _ _ ↦ rfl⟩
  · intro R hR hn _hReeb
    exact ⟨projection D R hn, fun _ _ ↦ rfl, projection_smooth D R hn hR,
      fun j hj ↦ zeroExtension_smooth D _ (projection_smooth D R hn hR) j hj⟩

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Transfer
