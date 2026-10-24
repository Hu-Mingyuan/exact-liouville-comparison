import ExactLiouvilleComparison.CylindricalCompatibilityContactAssembly
import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleStatement

/-! Exact identification of the reviewed contact maps with the native bundle
transfer interface. These lemmas explicitly take the transfer property; they
do not assert that a native kernel atlas has already been constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility
variable {d : ℕ} (D : LiouvilleDomain d) (B : ContactBundle.Prebundle D)
  (hB : ContactBundle.TransferProperties D B)
include hB

/-- Restriction of the actual supplied contact endomorphism is natively smooth. -/
theorem ContactData.kernelJ_smooth_of_transfer (P : ContactData D) :
    ContactBundle.SmoothKernelEndomorphism D B P.kernelJ := by
  obtain ⟨j, hj, heq⟩ := hB.1 P.J P.smooth_J (fun y v _ ↦ P.horizontal y v)
  have h : j = P.kernelJ := by
    funext y
    ext v : 1
    apply Subtype.ext
    exact heq y v
  exact h ▸ hj

/-- The transfer interface's projection equals the explicitly constructed Reeb
projection, as a native continuous linear map into the literal kernel. -/
theorem boundaryKernelProjection_smooth_of_transfer :
    letI : TopologicalSpace (TotalSpace (Model (d - 2)) (ContactBundle.Fiber D)) := B.totalSpaceTopology
    letI : FiberBundle (Model (d - 2)) (ContactBundle.Fiber D) := B.toFiberBundle
    letI : VectorBundle ℝ (Model (d - 2)) (ContactBundle.Fiber D) := B.toVectorBundle
    ContMDiff 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 1) →L[ℝ] Model (d - 2))) ∞
      (fun y ↦ TotalSpace.mk' (Model (d - 1) →L[ℝ] Model (d - 2)) y
        (boundaryKernelProjection D y)) := by
  obtain ⟨p, heq, hp, _⟩ := hB.2 (boundaryReeb D) (boundaryReeb_smooth D)
    (boundaryReeb_normalized D) (boundaryReeb_kernel D)
  have h : p = boundaryKernelProjection D := by
    funext y
    ext v : 1
    apply Subtype.ext
    exact heq y v
  exact h ▸ hp

/-- Smoothness applies to the literal zero extension used by contactDataOfKernel. -/
theorem extendKernelEndomorphism_smooth_of_transfer
    (j : (y : D.domain.boundary.Point) → ContactFiber D y →L[ℝ] ContactFiber D y)
    (hj : ContactBundle.SmoothKernelEndomorphism D B j) :
    SmoothEndomorphism D.domain.boundary (extendKernelEndomorphism D j) := by
  obtain ⟨p, heq, _, hz⟩ := hB.2 (boundaryReeb D) (boundaryReeb_smooth D)
    (boundaryReeb_normalized D) (boundaryReeb_kernel D)
  have h : p = boundaryKernelProjection D := by
    funext y
    ext v : 1
    apply Subtype.ext
    exact heq y v
  subst p
  exact hz j hj

end ExactLiouvilleComparison.CylindricalCompatibility
