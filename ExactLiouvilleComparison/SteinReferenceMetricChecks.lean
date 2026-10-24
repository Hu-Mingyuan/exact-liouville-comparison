import ExactLiouvilleComparison.SteinReferenceMetric

/-! Consumers of the bounded metric API, including the zero-dimensional case. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry

namespace ExactLiouvilleComparison.SteinReferenceMetric

/-- Every smooth map from a zero-dimensional manifold induces a metric: the
native derivative is injective without an additional hypothesis. -/
def zeroDimensionalMetric (M : SmoothManifold 0)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : M.Point → F) (hf : ContMDiff (𝓘(ℝ, Model 0)) (𝓘(ℝ, F)) ∞ f) :
    Bundle.ContMDiffRiemannianMetric (𝓘(ℝ, Model 0)) ∞ (Model 0) M.Tangent :=
  ofImmersion M f hf (fun _ _ _ _ => PiLp.ext (fun j => Fin.elim0 j))

/-- This consumer has exactly the field formula of `SteinReference.induced_metric`;
the primitive and compatibility construction are deliberately still the parent's work. -/
theorem stein_field_consumer {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) :
    ∀ x v w, (metric i).inner x v w =
      @inner ℝ (EuclideanSpace ℂ (Fin N)) _
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x w) :=
  metric_inner i

end ExactLiouvilleComparison.SteinReferenceMetric
