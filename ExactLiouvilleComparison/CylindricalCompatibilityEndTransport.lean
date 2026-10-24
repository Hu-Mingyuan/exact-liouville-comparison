import ExactLiouvilleComparison.CylindricalCompatibilityEndForm

/-! Pointwise transport of the prescribed end operator to the native ambient
tangent bundle. Global section smoothness and core extension are separate. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) (P : ContactData D)

/-- The actual end differential is a continuous linear equivalence. -/
def endTangentEquiv (y : D.domain.boundary.Point) (t : ℝ) :
    (D.domain.boundary.Tangent y × ℝ) ≃L[ℝ]
      C.ambient.manifold.Tangent (C.endMap (y, t)) :=
  (C.endMap_isLocalDiffeomorph (y, t)).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem endTangentEquiv_apply (y : D.domain.boundary.Point) (t : ℝ)
    (z : D.domain.boundary.Tangent y × ℝ) :
    endTangentEquiv C y t z =
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) z := rfl

/-- Construct the ambient end operator, rather than assume an end witness. -/
def endTangentJ (y : D.domain.boundary.Point) (t : ℝ) :
    C.ambient.manifold.Tangent (C.endMap (y, t)) →L[ℝ]
      C.ambient.manifold.Tangent (C.endMap (y, t)) :=
  (endTangentEquiv C y t).toContinuousLinearMap.comp
    ((P.endJ y).comp (endTangentEquiv C y t).symm.toContinuousLinearMap)

/-- The complete formula holds at every real time; in particular the seam and
all nonnegative end times will be retained by relative extension. -/
theorem endTangentJ_formula (y : D.domain.boundary.Point) (t : ℝ)
    (z : D.domain.boundary.Tangent y × ℝ) :
    endTangentJ C P y t (endTangentEquiv C y t z) =
      endTangentEquiv C y t (P.endJ y z) := by
  simp only [endTangentJ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem endTangentJ_square (y : D.domain.boundary.Point) (t : ℝ)
    (v : C.ambient.manifold.Tangent (C.endMap (y, t))) :
    endTangentJ C P y t (endTangentJ C P y t v) = -v := by
  obtain ⟨z, rfl⟩ := (endTangentEquiv C y t).surjective v
  rw [endTangentJ_formula, endTangentJ_formula, P.endJ_square, map_neg]

/-- Compatibility is with the actual ambient exterior derivative. -/
theorem endTangentJ_invariant (y : D.domain.boundary.Point) (t : ℝ)
    (v w : C.ambient.manifold.Tangent (C.endMap (y, t))) :
    evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
      (C.endMap (y, t)) (endTangentJ C P y t v) (endTangentJ C P y t w) =
    evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
      (C.endMap (y, t)) v w := by
  obtain ⟨z, rfl⟩ := (endTangentEquiv C y t).surjective v
  obtain ⟨u, rfl⟩ := (endTangentEquiv C y t).surjective w
  rw [endTangentJ_formula, endTangentJ_formula]
  simp only [endTangentEquiv_apply, end_twoForm]
  exact P.endPairing_invariant y t z u

theorem endTangentJ_positive (y : D.domain.boundary.Point) (t : ℝ)
    (v : C.ambient.manifold.Tangent (C.endMap (y, t))) (hv : v ≠ 0) :
    0 < evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
      (C.endMap (y, t)) v (endTangentJ C P y t v) := by
  obtain ⟨z, rfl⟩ := (endTangentEquiv C y t).surjective v
  have hz : z ≠ 0 := by
    intro hz
    exact hv (by rw [hz, map_zero])
  rw [endTangentJ_formula]
  simp only [endTangentEquiv_apply, end_twoForm]
  exact P.endPairing_positive y t z hz

end ExactLiouvilleComparison.CylindricalCompatibility
