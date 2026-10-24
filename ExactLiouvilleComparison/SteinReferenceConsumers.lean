import ExactLiouvilleComparison.SteinReference
import ExactLiouvilleComparison.SteinReferenceMetricChecks
import ExactLiouvilleComparison.SteinReferencePrimitiveConsumers

/-! Unconditional consumers of the full source-only construction. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.SteinReferenceConstruction

/-- The public constructor takes only the source embedding. -/
def sourceReferenceConsumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) : SteinReference i := reference i

/-- A consumer with the exact existing target type. -/
theorem targetConsumer : SteinReferenceConstructionTarget := construction

theorem checkedTargetConsumer : CheckedTarget := checkedConstruction

theorem referencePrimitiveConsumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) (x : M.Point) (v : M.Tangent x) :
    evalOne (sourceReferenceConsumer i).exactStructure.primitive x v =
      -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (i.J x v) :=
  (sourceReferenceConsumer i).primitive_eq x v

theorem referenceMetricConsumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) (x : M.Point) (v w : M.Tangent x) :
    (sourceReferenceConsumer i).compatible.g.inner x v w =
      @inner ℝ (EuclideanSpace ℂ (Fin N)) _
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x w) :=
  (sourceReferenceConsumer i).induced_metric x v w

theorem referenceDerivativeConsumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) :
    StandardDerivativeIdentity i (sourceReferenceConsumer i) := reference_standardDerivative i

/-- No dimension-positivity hypothesis is needed by the full construction. -/
def zeroDimensionsConsumer (M : SmoothManifold 0) (i : ProperComplexEmbedding M 0) :
    SteinReference i := reference i

end ExactLiouvilleComparison.SteinReferenceConstruction
