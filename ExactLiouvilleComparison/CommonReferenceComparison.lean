import ExactLiouvilleComparison.CorollaryComparisonStatement

/-! The common-reference corollary at independent growth hypotheses. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.CommonReferenceComparison

/-- Two applications of the actual main theorem, followed by exact algebra. -/
theorem commonReferenceTarget : CommonReferenceTarget := by
  intro d M P T₁ T₂ hw₁ hg₁ hw₂ hg₂
  exact (MainComparison.mainTarget d M P T₁ hw₁ hg₁).commonReference
    (MainComparison.mainTarget d M P T₂ hw₂ hg₂)

/-- Retain both actual endpoint/gauge witnesses and the literal Phi and q. -/
theorem explicitCommonTarget : CorollaryComparison.ExplicitCommonTarget := by
  intro d M P T₁ T₂ hw₁ hg₁ hw₂ hg₂
  obtain ⟨F₁, h₁, w₁⟩ :=
    (ExactComparisonAlgebra.exactComparison_iff_exists_witness _ _).mp
      (MainComparison.mainTarget d M P T₁ hw₁ hg₁)
  obtain ⟨F₂, h₂, w₂⟩ :=
    (ExactComparisonAlgebra.exactComparison_iff_exists_witness _ _).mp
      (MainComparison.mainTarget d M P T₂ hw₂ hg₂)
  exact ⟨F₁, F₂, h₁, h₂, w₁, w₂, w₁.commonReference w₂⟩

end ExactLiouvilleComparison.CommonReferenceComparison
