import ExactLiouvilleComparison.Statement

/-! Bounded induced-metric specification. No existence proof is asserted here. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry

namespace ExactLiouvilleComparison.SteinReferenceMetric

/-- The metric is a native smooth metric on the original tangent bundle, with
the literal real ambient inner product of the native derivatives. -/
def InducedMetricTarget {d : ℕ} (M : SmoothManifold d)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : M.Point → F) : Prop :=
  ∃ g : Bundle.ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent,
    ∀ x v w, g.inner x v w =
      @inner ℝ F _ (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x v)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x w)

/-- A construction contract, including zero dimensions, with no supplied metric. -/
def SmoothImmersionMetricTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (F : Type) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (f : M.Point → F),
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) ∞ f →
    (∀ x, Function.Injective (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x)) →
    InducedMetricTarget M f

/-- The original Stein input alone supplies the immersion data. -/
def ProperComplexMetricTarget : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N),
    InducedMetricTarget M i.map

end ExactLiouvilleComparison.SteinReferenceMetric
