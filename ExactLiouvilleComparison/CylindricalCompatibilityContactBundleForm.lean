import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAtlas
import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleFiber

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.FormInput

/-- Currying only in the normed chart model; no norm is imposed on tangent fibers. -/
def modelBilinear {n : ℕ} (eta : Model n [⋀^Fin 2]→L[ℝ] ℝ) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model n) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      eta.curryLeft

theorem modelBilinear_apply {n : ℕ} (eta : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (v w : Model n) : modelBilinear eta v w = eta ![v, w] := by
  change eta (Fin.cons v (fun _ : Fin 1 ↦ w)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

theorem modelBilinear_smooth (n : ℕ) : ContDiff ℝ ∞ (@modelBilinear n) := by
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model n [⋀^Fin 2]→L[ℝ] ℝ) → Model n →L[ℝ] Model n [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model n [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model n →L[ℝ] Model n [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Model n) (F := ℝ)
        (n := 1)).toContinuousLinearMap
  exact contDiff_const.clm_comp hcur

variable {d : ℕ} (D : LiouvilleDomain d)

def coefficient (x y : D.domain.boundary.Point) :
    Model (d - 1) →L[ℝ] Model (d - 1) →L[ℝ] ℝ :=
  modelBilinear (D.domain.boundary.formInChart x
    (D.domain.boundary.exteriorDerivative (boundaryAlpha D))
    (chartAt (Model (d - 1)) x y))

theorem coefficient_smooth (x : D.domain.boundary.Point) :
    ContMDiffOn 𝓘(ℝ, Model (d - 1))
      𝓘(ℝ, Model (d - 1) →L[ℝ] Model (d - 1) →L[ℝ] ℝ) ∞
      (coefficient D x) (Atlas.ambientChart D x).baseSet := by
  have hα : D.domain.boundary.IsSmoothForm (boundaryAlpha D) :=
    D.domain.boundary.isSmoothForm_pullback_one D.domain.extension
      D.domain.boundaryInclusion.map D.liouville.primitive D.liouville.smooth_primitive
  have hη := D.domain.boundary.isSmoothForm_exteriorDerivative (boundaryAlpha D) hα
  rw [TangentBundle.trivializationAt_baseSet]
  exact ((modelBilinear_smooth (d - 1)).comp_contDiffOn (hη x)).contMDiffOn.comp
    contMDiffOn_chart (chartAt (Model (d - 1)) x).mapsTo

theorem coefficient_apply (x y : D.domain.boundary.Point)
    (hy : y ∈ (Atlas.ambientChart D x).baseSet) (v w : Model (d - 1)) :
    coefficient D x y v w = evalTwo
      (D.domain.boundary.exteriorDerivative (boundaryAlpha D)) y
      ((Atlas.ambientChart D x).symmL ℝ y v)
      ((Atlas.ambientChart D x).symmL ℝ y w) := by
  rw [coefficient, modelBilinear_apply]
  unfold Atlas.ambientChart
  rw [TangentBundle.symmL_trivializationAt hy]
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, range_id,
    mfderivWithin_univ]
  let L := mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1))
    (chartAt (Model (d - 1)) x).symm (chartAt (Model (d - 1)) x y)
  change (D.domain.boundary.exteriorDerivative (boundaryAlpha D)
    ((chartAt (Model (d - 1)) x).symm (chartAt (Model (d - 1)) x y)))
    (L ∘ ![v, w]) =
      (D.domain.boundary.exteriorDerivative (boundaryAlpha D) y) ![L v, L w]
  have hp : L ∘ ![v, w] = ![L v, L w] := by
    funext i
    fin_cases i <;> rfl
  rw [hp]
  congr 1
  congr 1
  exact (chartAt (Model (d - 1)) x).left_inv hy


section Native
local instance : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) :=
  (Atlas.prebundle D).totalSpaceTopology
local instance : FiberBundle (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toFiberBundle
local instance : VectorBundle ℝ (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toVectorBundle
local instance : ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) :=
  Atlas.prebundle_smooth D

theorem differential_smooth :
    ContMDiff 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod
        𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 2) →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Model (d - 2) →L[ℝ] Model (d - 2) →L[ℝ] ℝ)
        y (differential D y)) := by
  intro x
  let e := trivializationAt (Model (d - 2)) (Fiber D) x
  let b := trivializationAt (Model (d - 2) →L[ℝ] Model (d - 2) →L[ℝ] ℝ)
    (fun y ↦ Fiber D y →L[ℝ] Fiber D y →L[ℝ] ℝ) x
  apply (b.contMDiffAt_section_iff (by
    simp only [b, hom_trivializationAt_baseSet]
    exact ⟨mem_baseSet_trivializationAt _ _ x,
      mem_baseSet_trivializationAt _ _ x, mem_univ x⟩)).mpr
  have hr := Atlas.reconstruction_smooth D x
  have hc := (coefficient_smooth D x).mono
    (t := Atlas.chartDomain D x) (fun _ hy ↦ hy.1)
  have hs : ContMDiffOn 𝓘(ℝ, Model (d - 1))
      𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 2) →L[ℝ] ℝ) ∞
      (fun y ↦ ((Atlas.reconstruction D x y).precomp ℝ).comp
        ((coefficient D x y).comp (Atlas.reconstruction D x y)))
      (Atlas.chartDomain D x) :=
    (hr.clm_precomp (F₃ := ℝ)).clm_comp (hc.clm_comp hr)
  apply (hs.contMDiffAt ((Atlas.chartDomain_open D x).mem_nhds
    (Atlas.mem_chartDomain D x))).congr_of_eventuallyEq
  filter_upwards [(Atlas.chartDomain_open D x).mem_nhds (Atlas.mem_chartDomain D x)] with y hy
  ext v w
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hy hy (by simp)]
  simp only [Trivialization.linearMapAt_apply]
  simp only [show (trivializationAt ℝ (fun _ : D.domain.boundary.Point ↦ ℝ) x).baseSet =
    univ from rfl, Set.mem_univ, ↓reduceIte]
  change differential D y (e.symm y v) (e.symm y w) =
    coefficient D x y (Atlas.reconstruction D x y v) (Atlas.reconstruction D x y w)
  rw [differential_eq_evalTwo, coefficient_apply D x y hy.1]
  rw [← e.symmL_apply (R := ℝ) hy v, ← e.symmL_apply (R := ℝ) hy w]
  rw [Atlas.native_symmL D x y hy, Atlas.native_symmL D x y hy,
    Atlas.coordinateEquiv_symm_ambient, Atlas.coordinateEquiv_symm_ambient]

end Native
end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.FormInput
