import ExactLiouvilleComparison.CylindricalCompatibilityExtension
import ExactLiouvilleComparison.CylindricalCompatibilityContactExistence
import ExactLiouvilleComparison.CylindricalCompatibilityBridges

/-! Existence and prescribed extension, with the original comparison consumer. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility

/-- Construct some compatible cylindrical structure, in every original dimension. -/
theorem existenceTarget : ExistenceTarget :=
  existence_of_contact_and_extension contactExistenceTarget extensionTarget

/-- The chosen J precedes the arbitrary weakly tamed exact symplectic target. -/
theorem consumerTarget : ConsumerTarget := consumer_of_existence existenceTarget

/-- Native smooth compatible contact-distribution data extend across the core.
This is distinct from choosing some contact data in `existenceTarget`. -/
theorem extension_of_prescribed_kernel {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D)
    (j : (y : D.domain.boundary.Point) → ContactFiber D y →L[ℝ] ContactFiber D y)
    (hj : ContactBundle.SmoothKernelEndomorphism D (ContactBundle.Atlas.prebundle D) j)
    (hsquare : ∀ y v, j y (j y v) = -v)
    (hinvariant : ∀ y v w,
      D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![j y v,j y w] =
      D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![v,w])
    (hpositive : ∀ y v, v ≠ 0 →
      0 < D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![v,j y v]) :
    ∃ A : CompatibleStructure (completionReference C),
      Nonempty (CylindricalStructure C A) ∧
      ∀ y t, 0 ≤ t → ∀ (v : D.domain.boundary.Tangent y) (s : ℝ),
        A.J (C.endMap (y,t))
          (mfderiv ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d))
            C.endMap (y,t) (v,s)) =
        mfderiv ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d))
          C.endMap (y,t)
          ((j y (boundaryKernelProjection D y v) : D.domain.boundary.Tangent y) +
            s • boundaryReeb D y, -evalOne (alpha D) y v) := by
  let P := contactDataOfKernel D j (extendKernelEndomorphism_smooth D j hj)
    hsquare hinvariant hpositive
  obtain ⟨A,hA⟩ := extension C P
  exact ⟨A,⟨hA.cylindrical⟩,hA⟩

end ExactLiouvilleComparison.CylindricalCompatibility
