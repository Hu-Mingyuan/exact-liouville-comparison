import ExactLiouvilleComparison.CylindricalCompatibilityContactAlgebra
import ExactLiouvilleComparison.CylindricalCompatibilityContactReebSmooth

/-! Algebraic assembly from an actual compatible kernel endomorphism.
The construction is conditional on that endomorphism and its smooth zero
extension. Existence of these inputs is a separate bundle/normalization task. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility
variable {d : ℕ} (D : LiouvilleDomain d)

/-- Projection using the constructed Reeb, with no compatible J input. -/
def boundaryProjection (y : D.domain.boundary.Point) :
    D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y :=
  ContinuousLinearMap.id ℝ _ - (alphaLinear D y).smulRight (boundaryReeb D y)

@[simp] theorem boundaryProjection_apply (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    boundaryProjection D y v = v - evalOne (alpha D) y v • boundaryReeb D y := rfl

private theorem boundaryProjection_mem (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) : boundaryProjection D y v ∈ ContactFiber D y := by
  change evalOne (alpha D) y (v - evalOne (alpha D) y v • boundaryReeb D y) = 0
  rw [evalOne_sub, evalOne_smul, boundaryReeb_normalized, mul_one, sub_self]

def boundaryKernelProjection (y : D.domain.boundary.Point) :
    D.domain.boundary.Tangent y →L[ℝ] ContactFiber D y :=
  (boundaryProjection D y).codRestrict _ (boundaryProjection_mem D y)

@[simp] theorem boundaryKernelProjection_coe (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    (boundaryKernelProjection D y v : D.domain.boundary.Tangent y) = boundaryProjection D y v := rfl

@[simp] theorem boundaryKernelProjection_of_mem (y : D.domain.boundary.Point)
    (v : ContactFiber D y) : boundaryKernelProjection D y v = v := by
  apply Subtype.ext
  have hv : evalOne (alpha D) y v = 0 := v.property
  change (v : D.domain.boundary.Tangent y) - evalOne (alpha D) y v • boundaryReeb D y = v
  rw [hv, zero_smul, sub_zero]

@[simp] theorem boundaryKernelProjection_reeb (y : D.domain.boundary.Point) :
    boundaryKernelProjection D y (boundaryReeb D y) = 0 := by
  apply Subtype.ext
  change boundaryReeb D y - evalOne (alpha D) y (boundaryReeb D y) • boundaryReeb D y = 0
  rw [boundaryReeb_normalized, one_smul, sub_self]

/-- Native continuous linear zero extension along the actual Reeb line. -/
def extendKernelEndomorphism
    (j : (y : D.domain.boundary.Point) → ContactFiber D y →L[ℝ] ContactFiber D y)
    (y : D.domain.boundary.Point) :
    D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y :=
  (ContactFiber D y).subtypeL.comp ((j y).comp (boundaryKernelProjection D y))

@[simp] theorem extendKernelEndomorphism_apply
    (j : (y : D.domain.boundary.Point) → ContactFiber D y →L[ℝ] ContactFiber D y)
    (y : D.domain.boundary.Point) (v : D.domain.boundary.Tangent y) :
    extendKernelEndomorphism D j y v = (j y (boundaryKernelProjection D y v) :
      D.domain.boundary.Tangent y) := rfl

private theorem differential_projection (y : D.domain.boundary.Point)
    (v w : D.domain.boundary.Tangent y) :
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y
      (boundaryProjection D y v) (boundaryProjection D y w) =
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v w := by
  rw [boundaryProjection_apply, evalTwo_sub_left, evalTwo_smul_left,
    boundaryReeb_kernel, mul_zero, sub_zero, boundaryProjection_apply,
    evalTwo_sub_right, evalTwo_smul_right]
  have hr : evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v (boundaryReeb D y) = 0 := by
    rw [evalTwo_swap, boundaryReeb_kernel, neg_zero]
  rw [hr, mul_zero, sub_zero]

/-- The reviewed contact-data package follows from a genuine compatible kernel
endomorphism and smoothness of its literal zero extension. This is an assembly
lemma, not an unconditional existence theorem. -/
def contactDataOfKernel
    (j : (y : D.domain.boundary.Point) → ContactFiber D y →L[ℝ] ContactFiber D y)
    (hsmooth : SmoothEndomorphism D.domain.boundary (extendKernelEndomorphism D j))
    (hsquare : ∀ y v, j y (j y v) = -v)
    (hinvariant : ∀ y v w,
      D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![j y v, j y w] =
      D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![v, w])
    (hpositive : ∀ y v, v ≠ 0 →
      0 < D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![v, j y v]) :
    ContactData D where
  reeb := boundaryReeb D
  smooth_reeb := boundaryReeb_smooth D
  normalized := boundaryReeb_normalized D
  kernel := boundaryReeb_kernel D
  J := extendKernelEndomorphism D j
  smooth_J := hsmooth
  annihilate_reeb := by
    intro y
    simp only [extendKernelEndomorphism_apply, boundaryKernelProjection_reeb, map_zero,
      Submodule.coe_zero]
  horizontal := by
    intro y v
    exact (j y (boundaryKernelProjection D y v)).property
  square := by
    intro y v
    rw [extendKernelEndomorphism_apply, extendKernelEndomorphism_apply,
      boundaryKernelProjection_of_mem, hsquare]
    change -(v - evalOne (alpha D) y v • boundaryReeb D y) = _
    abel
  invariant := by
    intro y v w
    have h := hinvariant y (boundaryKernelProjection D y v) (boundaryKernelProjection D y w)
    simp only [contactHyperplaneDifferential_apply] at h
    exact h.trans (differential_projection D y v w)
  positive := by
    intro y v hv hvne
    let u : ContactFiber D y := ⟨v, hv⟩
    have hu : u ≠ 0 := fun h => hvne (congrArg Subtype.val h)
    have h := hpositive y u hu
    rw [contactHyperplaneDifferential_apply] at h
    have hp : boundaryKernelProjection D y v = u := boundaryKernelProjection_of_mem D y u
    simpa only [extendKernelEndomorphism_apply, hp] using h

end ExactLiouvilleComparison.CylindricalCompatibility
