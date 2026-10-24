import ExactLiouvilleComparison.MoserExactnessIntegralEuclidean

noncomputable section
open scoped ContDiff
open Set MeasureTheory
namespace ExactLiouvilleComparison.MoserExactnessIntegralEuclidean

/-- Consumer for the parent's scalar chart integrals; no global strip is supplied. -/
theorem scalar_consumer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : ℝ × E → ℝ} {s : Set E} {U : Set (ℝ × E)}
    (hs : IsOpen s) (hU : IsOpen U) (hsub : Icc (0 : ℝ) 1 ×ˢ s ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) s ∧
    ∀ x ∈ s, HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, g (t, y))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => g (t, y)) x) x := by
  obtain ⟨h, hd⟩ := target E ℝ g s U hs hU hsub hg
  exact ⟨h, fun x hx => (hd x hx).2⟩

/-- Iterated-calculus consumer: the codomain can itself be a space of operators. -/
theorem operator_consumer {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : ℝ × E → E →L[ℝ] F} {s : Set E} {U : Set (ℝ × E)}
    (hs : IsOpen s) (hU : IsOpen U) (hsub : Icc (0 : ℝ) 1 ×ˢ s ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) s :=
  (target E (E →L[ℝ] F) g s U hs hU hsub hg).1

end ExactLiouvilleComparison.MoserExactnessIntegralEuclidean
