import ExactLiouvilleComparison.Statement

/-! Bounded construction contract. These definitions are specifications, not existence proofs. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.SteinReferenceConstruction

/-- Exactly the source-level target, without additional geometric inputs. -/
abbrev Target : Prop := SteinReferenceConstructionTarget

/-- The positive standard symplectic form on the image of the native derivative.
For the real inner product this is `-⟪di(v), I di(w)⟫`. -/
def StandardDerivativeIdentity {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) (P : SteinReference i) : Prop :=
  ∀ x v w, evalTwo (M.exteriorDerivative P.exactStructure.primitive) x v w =
    -@inner ℝ (EuclideanSpace ℂ (Fin N)) _
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
      (Complex.I • (show EuclideanSpace ℂ (Fin N) from mfderiv (𝓘(ℝ, Model d))
        (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x w))

/-- A strengthened output check, with the unchanged source inputs. -/
def CheckedTarget : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N),
    ∃ P : SteinReference i, StandardDerivativeIdentity i P

end ExactLiouvilleComparison.SteinReferenceConstruction
