import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationStatement
import ExactLiouvilleComparison.Geometry
import FsFltz.Geometry.SmoothLiouville
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! The actual native two-form as a smooth section of the bilinear Hom bundle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Bundle Set Filter

namespace ExactLiouvilleComparison.CylindricalCompatibility

/-- Currying retains literal two-form evaluation and its sign. -/
def twoFormBilinear {d : ℕ} {M : SmoothManifold d} (eta : M.Form 2) (x : M.Point) :
    M.Tangent x →L[ℝ] M.Tangent x →L[ℝ] ℝ :=
  by
  letI : NormedAddCommGroup (M.Tangent x) := inferInstanceAs (NormedAddCommGroup (Model d))
  letI : NormedSpace ℝ (M.Tangent x) := inferInstanceAs (NormedSpace ℝ (Model d))
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Model d) (F := ℝ)
    (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (eta x).curryLeft

@[simp] theorem twoFormBilinear_apply {d : ℕ} {M : SmoothManifold d}
    (eta : M.Form 2) (x : M.Point) (v w : M.Tangent x) :
    twoFormBilinear eta x v w = evalTwo eta x v w := by
  change eta x (Matrix.vecCons v (fun _ : Fin 1 => w)) = eta x ![v,w]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The pinned chartwise form regularity implies native Hom-bundle regularity. -/
theorem smooth_twoFormBilinear {d : ℕ} {M : SmoothManifold d}
    (eta : M.Form 2) (heta : M.IsSmoothForm eta) :
    ContMDiff (𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d →L[ℝ] Model d →L[ℝ] ℝ))) ∞
      (fun x => TotalSpace.mk' (Model d →L[ℝ] Model d →L[ℝ] ℝ) x
        (twoFormBilinear eta x)) := by
  intro a
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  have ha := mem_chart_source (Model d) a
  have ht := (chartAt (Model d) a).map_source ha
  have hcoeff := (heta a).contDiffAt ((chartAt (Model d) a).open_target.mem_nhds ht)
  have hchart := (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
    ((chartAt (Model d) a).open_source.mem_nhds ha)
  have hc := hcoeff.contMDiffAt.comp a hchart
  let curry : (Model d [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
      (Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    { toLinearMap := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Model d)
        (F := ℝ) (n := 1)).toLinearMap
      cont := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Model d)
        (F := ℝ) (n := 1)).continuous }
  have hcur : ContMDiffAt (𝓘(ℝ, Model d))
      𝓘(ℝ, Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) ∞
      (fun x => curry (M.formInChart a eta (chartAt (Model d) a x))) a := by
    have hs : ContMDiff 𝓘(ℝ, Model d [⋀^Fin 2]→L[ℝ] ℝ)
        𝓘(ℝ, Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) ∞ curry :=
      (ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
        (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) curry).contMDiff
    exact hs.contMDiffAt.comp a hc
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Model d)
    (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ContMDiffAt (𝓘(ℝ, Model d)) 𝓘(ℝ, (Model d [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ]
      (Model d →L[ℝ] ℝ)) ∞ (fun _ : M.Point => L) a := contMDiffAt_const
  apply (hL.clm_comp hcur).congr_of_eventuallyEq
  filter_upwards [(chartAt (Model d) a).open_source.mem_nhds ha] with x hx
  ext v w
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [ContinuousLinearMap.comp_apply, twoFormBilinear_apply]
  rw [← (trivializationAt (Model d) M.Tangent a).symmL_apply (R := ℝ) hx v,
    ← (trivializationAt (Model d) M.Tangent a).symmL_apply (R := ℝ) hx w]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  change evalTwo eta x
      ((trivializationAt (Model d) M.Tangent a).symmL ℝ x v)
      ((trivializationAt (Model d) M.Tangent a).symmL ℝ x w) = _
  rw [TangentBundle.symmL_trivializationAt hx]
  simp only [mfld_simps, mfderivWithin_univ]
  dsimp [L, curry, formInChart, evalTwo]
  rw [(chartAt (Model d) a).left_inv hx]
  apply congrArg (eta x)
  ext i
  fin_cases i <;> rfl

local instance tangentNormedAddCommGroup {d : ℕ} (M : SmoothManifold d) :
    ∀ x : M.Point, NormedAddCommGroup (M.Tangent x) := fun _ ↦ inferInstanceAs (NormedAddCommGroup (Model d))
local instance tangentNormedSpace {d : ℕ} (M : SmoothManifold d) :
    ∀ x : M.Point, NormedSpace ℝ (M.Tangent x) := fun _ ↦ inferInstanceAs (NormedSpace ℝ (Model d))

/-- Native alternating nondegenerate bundle form from the actual exact symplectic data. -/
def referenceBundleForm {d : ℕ} {M : SmoothManifold d} (S : ExactSymplecticStructure M) :
    Normalization.SymplecticForm (𝓘(ℝ, Model d)) (Model d) M.Tangent where
  form := twoFormBilinear (M.exteriorDerivative S.primitive)
  smooth := smooth_twoFormBilinear _ S.symplectic.1
  alternating x v := by
    rw [twoFormBilinear_apply]
    exact (M.exteriorDerivative S.primitive x).map_eq_zero_of_eq ![v,v]
      (by simp) (by decide : (0 : Fin 2) ≠ 1)
  nondegenerate x v hv := S.symplectic.2.2 x (mem_univ x) v
    (by simpa only [twoFormBilinear_apply] using hv)

@[simp] theorem referenceBundleForm_apply {d : ℕ} {M : SmoothManifold d}
    (S : ExactSymplecticStructure M) (x : M.Point) (v w : M.Tangent x) :
    (referenceBundleForm S).form x v w =
      evalTwo (M.exteriorDerivative S.primitive) x v w :=
  twoFormBilinear_apply _ x v w

end ExactLiouvilleComparison.CylindricalCompatibility
