import ExactLiouvilleComparison.CylindricalCompatibilityContactSmoothBridges
import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleInputs
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationBundle

/-! Construction of the reviewed contact data from the actual smooth kernel
bundle, its constructed auxiliary metric and supplied-metric normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open Bundle
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility
open ContactBundle
variable {d : ℕ} (D : LiouvilleDomain d)

local instance : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) :=
  (Atlas.prebundle D).totalSpaceTopology
local instance : FiberBundle (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toFiberBundle
local instance : VectorBundle ℝ (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toVectorBundle
local instance : ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) :=
  Atlas.prebundle_smooth D
local instance : RiemannianBundle (Fiber D) := ⟨(Inputs.metric D).toRiemannianMetric⟩

/-- Actual smooth compatible endomorphism of the native boundary kernel. -/
def compatibleKernelJ (y : D.domain.boundary.Point) : ContactFiber D y →L[ℝ] ContactFiber D y :=
  Normalization.normalizedEndomorphism (Inputs.form D) (Inputs.metric D) y

theorem compatibleKernelJ_smooth :
    SmoothKernelEndomorphism D (Atlas.prebundle D) (compatibleKernelJ D) :=
  Normalization.normalizedEndomorphism_contMDiff (Inputs.form D) (Inputs.metric D)

theorem compatibleKernelJ_compatible (y : D.domain.boundary.Point) :
    Normalization.Compatible (differential D y) (compatibleKernelJ D y) :=
  Normalization.normalizedEndomorphism_compatible (Inputs.form D) (Inputs.metric D) y

/-- The canonical contact constructor has no supplied Reeb, J, frame, metric,
bundle, or completeness input. -/
def contactData : ContactData D :=
  contactDataOfKernel D (compatibleKernelJ D)
    (extendKernelEndomorphism_smooth_of_transfer D (Atlas.prebundle D)
      (Transfer.transferProperties D) _ (compatibleKernelJ_smooth D))
    (fun y ↦ (compatibleKernelJ_compatible D y).1)
    (fun y v w ↦ by
      simpa only [← differential_apply] using (compatibleKernelJ_compatible D y).2.1 v w)
    (fun y v hv ↦ by
      simpa only [← differential_apply] using (compatibleKernelJ_compatible D y).2.2 v hv)

/-- The archived contact nonvacuity target, in every dimension and empty case. -/
theorem contactExistenceTarget : ContactExistenceTarget :=
  fun _ D _C ↦ ⟨contactData D⟩

/-- The prescribed contact-data interpretation is a native smooth kernel section. -/
theorem ContactData.kernelJ_smooth (P : ContactData D) :
    SmoothKernelEndomorphism D (Atlas.prebundle D) P.kernelJ :=
  ContactData.kernelJ_smooth_of_transfer D (Atlas.prebundle D) (Transfer.transferProperties D) P

/-- Native smooth zero extension for every smooth kernel endomorphism, using
the actual constructed Reeb projection. -/
theorem extendKernelEndomorphism_smooth
    (j : (y : D.domain.boundary.Point) → ContactFiber D y →L[ℝ] ContactFiber D y)
    (hj : SmoothKernelEndomorphism D (Atlas.prebundle D) j) :
    SmoothEndomorphism D.domain.boundary (extendKernelEndomorphism D j) :=
  extendKernelEndomorphism_smooth_of_transfer D (Atlas.prebundle D)
    (Transfer.transferProperties D) j hj

end ExactLiouvilleComparison.CylindricalCompatibility
