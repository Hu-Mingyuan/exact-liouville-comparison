import ExactLiouvilleComparison.FiniteTypeRadial
import ExactLiouvilleComparison.FiniteTypeRadialMetricChecks

noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.FiniteTypeRadial
variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
  (A : CompatibleStructure (completionReference C)) (cyl : CylindricalStructure C A)

theorem reference_exactStructure : (reference C A cyl).exactStructure = completionReference C := rfl
theorem reference_compatible : (reference C A cyl).compatible = A := rfl
theorem reference_primitive : (reference C A cyl).exactStructure.primitive = C.ambient.primitive := rfl
theorem reference_J : (reference C A cyl).compatible.J = A.J := rfl
theorem reference_g : (reference C A cyl).compatible.g = A.g := rfl
theorem reference_radius : (reference C A cyl).R = radius C := rfl
theorem reference_c : (reference C A cyl).c = 1 := rfl
theorem reference_rstar : (reference C A cyl).rstar = 2 := rfl

/-- The native derivative formula is a consequence at the actual constructed R. -/
theorem constructed_end_derivative (y : D.domain.boundary.Point) (t : ℝ)
    (ht : Real.log 2 < t) (v : D.domain.boundary.Tangent y) (s : ℝ) :
    C.ambient.manifold.scalarDerivative (reference C A cyl).R (C.endMap (y,t))
      (mfderiv ((𝓘(ℝ, Model (d-1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (y,t) (v,s)) = Real.exp t * s :=
  FiniteTypeRadialMetric.radius_end_derivative C (radius C) (radius_smooth C)
    (radius_end_eq C) y t ht v s

/-- Explicit fixed-witness consumer: B and C₀ are unchanged. -/
theorem constructed_growth_witness (T : ExactSymplecticStructure C.ambient.manifold)
    (B : AdmissibleGrowth 1) (C₀ t₀ : ℝ)
    (h : ∀ y t, t₀ ≤ t → A.inverseNorm T (C.endMap (y,t)) ≤ C₀ * B.B (Real.exp t)) :
    ∃ K : Set C.ambient.manifold.Point, IsCompact K ∧
      ∀ x, x ∉ K → A.inverseNorm T x ≤ C₀ * B.B ((reference C A cyl).R x) :=
  growth_witness (constructedRadius C A cyl) T B C₀ t₀ h

theorem checked_construction : ConstructionTarget := constructionTarget
theorem checked_growth : GrowthWitnessTarget := growthWitnessTarget
theorem checked_consumer : ConsumerTarget := consumerTarget

end ExactLiouvilleComparison.FiniteTypeRadial
