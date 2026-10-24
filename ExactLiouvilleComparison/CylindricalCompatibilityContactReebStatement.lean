import ExactLiouvilleComparison.CylindricalCompatibilityStatement
import FsFltz.Geometry.SmoothLiouville
import FsFltz.Geometry.BoundaryContactDistribution

noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility

/-- Precisely the first four fields of the accepted contact data, with no J input. -/
def ReebExistenceTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d),
    ∃ R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y,
      D.domain.boundary.IsSmoothVectorField R ∧
      (∀ y, evalOne (alpha D) y (R y) = 1) ∧
      (∀ y v, evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y (R y) v = 0)

/-- The augmented contraction operator. Euclidean Riesz is only an auxiliary
identification for matrix inversion; it specifies no geometric reference metric. -/
def augmentedContactOperator {n : ℕ}
    (a : Model n [⋀^Fin 1]→L[ℝ] ℝ) (b : Model n [⋀^Fin 2]→L[ℝ] ℝ) :
    (Model n × ℝ) →L[ℝ] (Model n × ℝ) :=
  ((chartContraction b).comp (ContinuousLinearMap.fst ℝ (Model n) ℝ) +
    (ContinuousLinearMap.snd ℝ (Model n) ℝ).smulRight ((chartOneFormEquiv n).symm a)).prod
    (((ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)).symm a).comp
      (ContinuousLinearMap.fst ℝ (Model n) ℝ))

end ExactLiouvilleComparison.CylindricalCompatibility
