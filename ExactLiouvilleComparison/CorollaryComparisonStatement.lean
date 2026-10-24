import ExactLiouvilleComparison.MainComparison
import ExactLiouvilleComparison.SteinReference
import ExactLiouvilleComparison.SteinRadial
import ExactLiouvilleComparison.SteinGrowthConsumers

/-! Bounded application specifications, not proofs of the corollaries. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.CorollaryComparison

abbrev PackagedTarget : Prop := PackagedSteinTarget
abbrev SourceTarget : Prop := SteinTarget
abbrev CommonTarget : Prop := CommonReferenceTarget

/-- The source reference is the delivered construction from the embedding alone. -/
def ConstructedSteinTarget : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N)
    (T : ExactSymplecticStructure M),
    let P := SteinReferenceConstruction.reference i
    WeaklyTames P.compatible T →
    GrowthAtInfinity P.compatible T (steinRadius i) (Real.exp 1) →
    ExactComparison M T.primitive P.exactStructure.primitive

/-- Two independently obtained comparison witnesses and the literal manuscript
map and gauge, including the native isotopy and exterior identity. -/
def ExplicitCommonTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
    (T₁ T₂ : ExactSymplecticStructure M),
    WeaklyTames P.compatible T₁ → GrowthAtInfinity P.compatible T₁ P.R 1 →
    WeaklyTames P.compatible T₂ → GrowthAtInfinity P.compatible T₂ P.R 1 →
    ∃ (F₁ F₂ : M.SmoothEquiv M) (h₁ h₂ : M.Point → ℝ),
      ExactComparisonAlgebra.Witness M T₁.primitive P.exactStructure.primitive F₁ h₁ ∧
      ExactComparisonAlgebra.Witness M T₂.primitive P.exactStructure.primitive F₂ h₂ ∧
      ExactComparisonAlgebra.Witness M T₁.primitive T₂.primitive
        (F₂.symm.trans F₁) (fun x => (h₁ - h₂) (F₂.symm x))

end ExactLiouvilleComparison.CorollaryComparison
