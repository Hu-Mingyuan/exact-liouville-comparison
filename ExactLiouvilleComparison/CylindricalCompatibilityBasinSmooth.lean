import ExactLiouvilleComparison.CylindricalCompatibilityTransportSmooth
import ExactLiouvilleComparison.CylindricalCompatibilityProductSmooth
import FsFltz.Geometry.CompletionIntervalMapFamily

/-! The prescribed operator on the actual open escaping basin. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Bundle Set Filter ContinuousLinearMap

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) (P : ContactData D)

theorem smooth_endTangentJ :
    ContMDiff ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d →L[ℝ] Model d)) ∞
      (fun q : D.domain.boundary.Point × ℝ => TotalSpace.mk'
        (Model d →L[ℝ] Model d)
        (E := fun x => C.ambient.manifold.Tangent x →L[ℝ] C.ambient.manifold.Tangent x)
        (C.endMap q) (endTangentJ C P q.1 q.2)) := by
  have h := smooth_transportEndomorphism
    ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d))
    C.endMap C.smooth_endMap (fun q => (C.endMap_isLocalDiffeomorph q).isInvertible_mfderiv (by simp))
    (fun q => P.endJ q.1) P.smooth_endJ
  convert h using 1
  funext q
  congr 1
  unfold endTangentJ transportEndomorphism
  change (endTangentEquiv C q.1 q.2).toContinuousLinearMap.comp
      ((P.endJ q.1).comp (endTangentEquiv C q.1 q.2).symm.toContinuousLinearMap) =
    (endTangentEquiv C q.1 q.2).toContinuousLinearMap.comp
      ((P.endJ q.1).comp (endTangentEquiv C q.1 q.2).toContinuousLinearMap.inverse)
  rw [ContinuousLinearMap.inverse_equiv]

/-- Extend by zero only as a total section for the relative gluing input.
Smoothness is asserted on the actual open basin, where this is prescribed data. -/
def endJOn (x : C.ambient.manifold.Point) :
    C.ambient.manifold.Tangent x →L[ℝ] C.ambient.manifold.Tangent x := by
  classical
  exact if hx : x ∈ C.escapingBasin then
    endTangentJ C P (C.endCoordinates ⟨x,hx⟩).1 (C.endCoordinates ⟨x,hx⟩).2
  else 0

@[simp] theorem endJOn_endMap (y : D.domain.boundary.Point) (t : ℝ) :
    endJOn C P (C.endMap (y,t)) = endTangentJ C P y t := by
  have hx : C.endMap (y,t) ∈ C.escapingBasin := ⟨(y,t),rfl⟩
  simp only [endJOn, dif_pos hx]
  change endTangentJ C P (C.endCoordinates (C.endInBasin (y,t))).1
    (C.endCoordinates (C.endInBasin (y,t))).2 = _
  rw [C.endCoordinates_endInBasin]

/-- Smoothness as an ambient tangent Hom section throughout the two-sided collar. -/
theorem smoothOn_endJOn :
    ContMDiffOn (𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d →L[ℝ] Model d)) ∞
      (fun x => TotalSpace.mk' (Model d →L[ℝ] Model d) x (endJOn C P x))
      C.escapingBasin := by
  have h := (smooth_endTangentJ C P).comp C.contMDiff_endCoordinates
  have he : (fun z : C.escapingBasin => TotalSpace.mk'
        (Model d →L[ℝ] Model d) z.val (endJOn C P z.val)) =
      (fun q : D.domain.boundary.Point × ℝ => TotalSpace.mk'
        (Model d →L[ℝ] Model d)
        (E := fun x => C.ambient.manifold.Tangent x →L[ℝ] C.ambient.manifold.Tangent x)
        (C.endMap q) (endTangentJ C P q.1 q.2)) ∘ C.endCoordinates := by
    funext z
    dsimp only [Function.comp_def]
    rw [← endJOn_endMap, C.endMap_endCoordinates]
  rw [← he] at h
  intro x hx
  exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, Model d))
    (I' := (𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d →L[ℝ] Model d))
    (U := C.escapingBasin)
    (f := fun z : C.ambient.manifold.Point => TotalSpace.mk'
      (Model d →L[ℝ] Model d) z (endJOn C P z))
    (x := ⟨x,hx⟩)).mp (h ⟨x,hx⟩) |>.contMDiffWithinAt

/-- The full closed nonnegative end, including its seam, is the relative set. -/
def closedEnd : Set C.ambient.manifold.Point :=
  C.endMap '' (univ ×ˢ Ici (0 : ℝ))

theorem isClosed_closedEnd : IsClosed (closedEnd C) :=
  C.isClosed_endMap_image_Ici 0

theorem closedEnd_subset_basin : closedEnd C ⊆ C.escapingBasin := by
  rintro x ⟨q,hq,rfl⟩
  exact ⟨q,rfl⟩

end ExactLiouvilleComparison.CylindricalCompatibility
