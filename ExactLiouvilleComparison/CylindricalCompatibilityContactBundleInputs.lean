import ExactLiouvilleComparison.CylindricalCompatibilityContactBundle
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationStatement

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open Bundle
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Inputs

variable {d : ℕ} (D : LiouvilleDomain d)
local instance : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) :=
  (Atlas.prebundle D).totalSpaceTopology
local instance : FiberBundle (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toFiberBundle
local instance : VectorBundle ℝ (Model (d - 2)) (Fiber D) := (Atlas.prebundle D).toVectorBundle
local instance : ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) :=
  Atlas.prebundle_smooth D

/-- A constructed auxiliary smooth metric on the actual kernel. It is not the
manuscript reference metric, and it is not chosen from an assumed J. -/
def metric : ContMDiffRiemannianMetric 𝓘(ℝ, Model (d - 1)) ∞ (Model (d - 2)) (Fiber D) :=
  Classical.choice (metric_of_atlas D (Atlas.prebundle D) (Atlas.atlasProperties D))

local instance : RiemannianBundle (Fiber D) := ⟨(metric D).toRiemannianMetric⟩

/-- Literal d-alpha with the accepted normalization sibling's native input type.
The metric-induced norm preserves the existing kernel topology. -/
def form : Normalization.SymplecticForm 𝓘(ℝ, Model (d - 1)) (Model (d - 2)) (Fiber D) where
  form := differential D
  smooth := FormInput.differential_smooth D
  alternating := differential_alternating D
  nondegenerate := differential_nondegenerate D

theorem form_apply (y : D.domain.boundary.Point) (v w : Fiber D y) :
    (form D).form y v w =
      evalTwo (D.domain.boundary.exteriorDerivative (boundaryAlpha D)) y v w :=
  differential_eq_evalTwo D y v w

theorem norm_eq (y : D.domain.boundary.Point) (v : Fiber D y) :
    ‖v‖ = Real.sqrt ((metric D).inner y v v) := rfl

theorem smooth_riemannian :
    IsContMDiffRiemannianBundle 𝓘(ℝ, Model (d - 1)) ∞ (Model (d - 2)) (Fiber D) := by
  infer_instance

/-- The accepted normalization target is well-typed for these actual inputs.
No normalization or compatible J is constructed by this mission. -/
def normalizationInputTarget : Prop :=
  Normalization.NormalizationTarget 𝓘(ℝ, Model (d - 1)) (Model (d - 2)) (Fiber D)
    (form D) (metric D)

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Inputs
