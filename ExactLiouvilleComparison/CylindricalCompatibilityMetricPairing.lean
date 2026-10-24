import ExactLiouvilleComparison.CylindricalCompatibilityFormBridge
import FsFltz.Geometry.BoundaryContactDistribution

/-! The explicit bilinear metric pairing eta(.,J.), in the native Hom bundle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Bundle Set Filter ContinuousLinearMap

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {d : ℕ} {M : SmoothManifold d}

local instance : ∀ x : M.Point, NormedAddCommGroup (M.Tangent x) :=
  fun _ ↦ inferInstanceAs (NormedAddCommGroup (Model d))
local instance : ∀ x : M.Point, NormedSpace ℝ (M.Tangent x) :=
  fun _ ↦ inferInstanceAs (NormedSpace ℝ (Model d))

/-- No reference metric is substituted for the required output metric. -/
def metricPairing (eta : M.Form 2)
    (J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x) (x : M.Point) :
    M.Tangent x →L[ℝ] M.Tangent x →L[ℝ] ℝ :=
  (J x).precomp ℝ |>.comp (twoFormBilinear eta x)

@[simp] theorem metricPairing_apply (eta : M.Form 2)
    (J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x)
    (x : M.Point) (v w : M.Tangent x) :
    metricPairing eta J x v w = evalTwo eta x v (J x w) :=
  twoFormBilinear_apply eta x v (J x w)

/-- Point-local regularity, usable both globally and on the open end. -/
theorem smoothAt_metricPairing (eta : M.Form 2) (heta : M.IsSmoothForm eta)
    (J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x) (a : M.Point)
    (hJ : ContMDiffAt (𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d →L[ℝ] Model d)) ∞
      (fun x => TotalSpace.mk' (Model d →L[ℝ] Model d) x (J x)) a) :
    ContMDiffAt (𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d →L[ℝ] Model d →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (Model d →L[ℝ] Model d →L[ℝ] ℝ) x
        (metricPairing eta J x)) a := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hB := ((contMDiffAt_hom_bundle _).mp (smooth_twoFormBilinear eta heta a)).2
  have hK := ((contMDiffAt_hom_bundle _).mp hJ).2
  apply ((hK.clm_precomp (F₃ := ℝ)).clm_comp hB).congr_of_eventuallyEq
  filter_upwards [(trivializationAt (Model d) M.Tangent a).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' a)] with x hx
  ext v w
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp), inCoordinates_eq hx hx]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    metricPairing_apply, twoFormBilinear_apply]
  change _ = (Trivialization.linearMapAt ℝ (trivializationAt ℝ (fun _ : M.Point => ℝ) a) x)
    (evalTwo eta x _ (((trivializationAt (Model d) M.Tangent a).continuousLinearEquivAt ℝ x hx).symm
      (((trivializationAt (Model d) M.Tangent a).continuousLinearEquivAt ℝ x hx) _)))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- Compatibility gives symmetry with the manuscript's positive convention. -/
theorem metricPairing_symm (eta : M.Form 2)
    (J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x)
    (x : M.Point)
    (hsq : ∀ v, J x (J x v) = -v)
    (hinv : ∀ v w, evalTwo eta x (J x v) (J x w) = evalTwo eta x v w)
    (v w : M.Tangent x) :
    metricPairing eta J x v w = metricPairing eta J x w v := by
  simp only [metricPairing_apply]
  have h := hinv (J x v) w
  rw [hsq] at h
  have hn : evalTwo eta x (-v) (J x w) = -evalTwo eta x v (J x w) := by
    simpa only [neg_one_smul, neg_one_mul] using evalTwo_smul_left eta x (-1) v (J x w)
  rw [hn, evalTwo_swap eta x (J x v) w] at h
  exact neg_injective h

end ExactLiouvilleComparison.CylindricalCompatibility
