import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleForm
import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleMetric
import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleTransfer

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle

theorem nativeProperties {d : ℕ} (D : LiouvilleDomain d) :
    NativeProperties D (Atlas.prebundle D) :=
  ⟨Atlas.atlasProperties D, FormInput.differential_smooth D,
    differential_alternating D, differential_nondegenerate D,
    metric_of_atlas D (Atlas.prebundle D) (Atlas.atlasProperties D)⟩

/-- Full unconditional kernel-bundle construction, in every natural dimension.
Reeb fields enter only as supplied arguments to the proved transfer property. -/
theorem bundleExistence : BundleExistenceTarget :=
  fun _ D ↦ ⟨Atlas.prebundle D, nativeProperties D, Transfer.transferProperties D⟩

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle
