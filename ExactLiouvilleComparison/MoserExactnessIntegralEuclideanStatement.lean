import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Bounded analytic contract. `Target` is a statement, not a proof. -/
noncomputable section
open scoped ContDiff
open Set MeasureTheory
namespace ExactLiouvilleComparison.MoserExactnessIntegralEuclidean

/-- Smooth compact-interval integration on a local open joint domain. -/
def Target : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ × E → F) (s : Set E) (U : Set (ℝ × E)),
    IsOpen s → IsOpen U → Icc (0 : ℝ) 1 ×ˢ s ⊆ U → ContDiffOn ℝ ∞ g U →
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) s ∧
    ∀ x ∈ s,
      IntervalIntegrable (fun t => fderiv ℝ (fun y => g (t, y)) x) volume 0 1 ∧
      HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, g (t, y))
        (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => g (t, y)) x) x

end ExactLiouvilleComparison.MoserExactnessIntegralEuclidean
