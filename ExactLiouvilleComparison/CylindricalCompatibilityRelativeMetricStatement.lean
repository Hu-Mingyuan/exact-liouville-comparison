import ExactLiouvilleComparison.CylindricalCompatibilityRelativeSection

/-! Native contracts for relative smooth Riemannian metric extension.
These propositions specify obligations; they do not assert their proofs. -/
noncomputable section
open Bundle Set FsFltz.Geometry
open scoped Manifold ContDiff

namespace ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric

abbrev BilinField {d : ℕ} (M : SmoothManifold d) :=
  (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x →L[ℝ] ℝ

abbrev NativeMetric {d : ℕ} (M : SmoothManifold d) :=
  Bundle.ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent

/-- Smoothness in the actual iterated Hom bundle, only on the specified set. -/
def SmoothOn {d : ℕ} (M : SmoothManifold d) (q : BilinField M) (U : Set M.Point) : Prop :=
  ContMDiffOn (𝓘(ℝ, Model d))
    ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d →L[ℝ] Model d →L[ℝ] ℝ)) ∞
    (fun x => TotalSpace.mk' (Model d →L[ℝ] Model d →L[ℝ] ℝ) x (q x)) U

/-- No global metric or local positive-section input. K can be empty or all of M. -/
def RelativeMetricTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (K U : Set M.Point),
    IsClosed K → IsOpen U → K ⊆ U →
    ∀ q : BilinField M, SmoothOn M q U → (∀ x ∈ U, SPD (q x)) →
    ∃ g : NativeMetric M, ∀ x ∈ K, g.inner x = q x

/-- Native global SPD section conversion, for the parent's omega(.,J.) field. -/
def SPDMetricTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (q : BilinField M),
    SmoothOn M q univ → (∀ x, SPD (q x)) →
    ∃ g : NativeMetric M, ∀ x, g.inner x = q x

end ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric
