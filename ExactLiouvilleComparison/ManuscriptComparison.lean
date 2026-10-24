import ExactLiouvilleComparison.ManuscriptComparisonStatement
import ExactLiouvilleComparison.FiniteTypeComparison

/-! Actual proofs of all four unchanged manuscript statements and the complete specialization. -/
namespace ExactLiouvilleComparison.ManuscriptComparison

/-- Each component is an actual unconditional proof at the original hypotheses. -/
theorem manuscriptTarget : ManuscriptTarget :=
  ⟨MainComparison.mainTarget, FiniteTypeComparison.finiteTypeTarget,
    SteinComparison.steinTarget, CommonReferenceComparison.commonReferenceTarget⟩

/-- The complete flows belong to the prescribed primitives. The general theorem
needs no such assumption and remains unchanged. -/
theorem completeLiouvilleComparisonTarget : CompleteLiouvilleComparisonTarget := by
  intro d M P _ T _ hw hg
  exact MainComparison.mainTarget d M P T hw hg

end ExactLiouvilleComparison.ManuscriptComparison
