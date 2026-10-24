import ExactLiouvilleComparison.SteinReferencePrimitive

noncomputable section
open scoped Manifold
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.SteinReferenceConstruction

/-- Unconditional source-only exact-symplectic consumer; metric assembly is separate. -/
def sourceExactConsumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) : ExactSymplecticStructure M := exactStructure i

theorem sourcePrimitiveConsumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) (x : M.Point) (v : M.Tangent x) :
    evalOne (sourceExactConsumer i).primitive x v =
      -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (i.J x v) :=
  primitive_eq i x v

/-- The symplectic pairing is literally the induced real inner product. -/
theorem sourcePairingConsumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (sourceExactConsumer i).primitive) x v (i.J x w) =
      @inner ℝ (EuclideanSpace ℂ (Fin N)) _
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x w) := by
  convert! compatible_value i x v w using 1

end ExactLiouvilleComparison.SteinReferenceConstruction
