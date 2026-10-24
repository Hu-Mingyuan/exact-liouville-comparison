import ExactLiouvilleComparison.SteinReferencePrimitive
import ExactLiouvilleComparison.SteinReferenceMetric

/-! The source-only Stein reference construction for the unchanged manuscript setup. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.SteinReferenceConstruction
variable {d N : ℕ} {M : SmoothManifold d}

/-- Compatibility with the actual induced native smooth metric. -/
def compatible (i : ProperComplexEmbedding M N) : CompatibleStructure (exactStructure i) where
  J := i.J
  smooth_J := i.smooth_J
  square := i.square
  invariant := invariant i
  g := SteinReferenceMetric.metric i
  metric_eq x v w := by
    rw [SteinReferenceMetric.metric_inner]
    exact (compatible_value i x v w).symm

/-- Construct all Stein reference data from the original embedding alone. -/
def reference (i : ProperComplexEmbedding M N) : SteinReference i where
  exactStructure := exactStructure i
  compatible := compatible i
  complex_eq := rfl
  primitive_eq := primitive_eq i
  induced_metric := SteinReferenceMetric.metric_inner i

/-- The constructed reference has the actual induced standard symplectic derivative. -/
theorem reference_standardDerivative (i : ProperComplexEmbedding M N) :
    StandardDerivativeIdentity i (reference i) := by
  intro x v w
  exact exteriorDerivative_apply i x v w

/-- The unchanged source-level construction obligation, now proved. -/
theorem construction : SteinReferenceConstructionTarget := by
  intro d N M i
  exact ⟨reference i⟩

/-- The reviewed strengthened output check, with no additional hypotheses. -/
theorem checkedConstruction : CheckedTarget := by
  intro d N M i
  exact ⟨reference i, reference_standardDerivative i⟩

end ExactLiouvilleComparison.SteinReferenceConstruction
