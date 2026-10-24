import ExactLiouvilleComparison.MainComparison
import ExactLiouvilleComparison.FiniteTypeRadial

/-! Bounded application specifications; these definitions do not prove the targets. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FiniteTypeComparison

abbrev ApplicationTarget : Prop := FiniteTypeTarget

/-- The explicit native conclusion to expose after applying the actual theorem. -/
def NativeConclusion {d : ℕ} (M : SmoothManifold d) (source target : M.Form 1) : Prop :=
  ∃ (F : M.SmoothEquiv M) (h : M.Point → ℝ) (H : ℝ → M.SmoothEquiv M),
    (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F x) ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × M.Point => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × M.Point => (H p.1).symm p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ h ∧
    (∀ x v, evalOne (M.pullback M F source) x v =
      evalOne target x v + M.scalarDerivative h x v) ∧
    M.pullback M F (M.exteriorDerivative source) = M.exteriorDerivative target

end ExactLiouvilleComparison.FiniteTypeComparison
