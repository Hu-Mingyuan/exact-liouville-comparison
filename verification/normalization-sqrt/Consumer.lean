import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationSqrt

noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff
open ExactLiouvilleComparison.NormalizationSqrt

namespace NormalizationSqrtConsumer
variable {n : Type*} [Fintype n] [DecidableEq n]

-- A nonconstant family at every positive rank, with positivity proved from a polynomial.
theorem polynomial_family_smooth :
    ContDiff ℝ ∞ (fun t : ℝ =>
      CFC.sqrt ((t ^ 2 + 1) • (1 : Matrix n n ℝ))) := by
  apply contDiff_sqrt_comp
  · fun_prop
  · intro t
    exact Matrix.PosDef.one.smul (by positivity)

theorem polynomial_inverse_family_smooth :
    ContDiff ℝ ∞ (fun t : ℝ =>
      Ring.inverse (CFC.sqrt ((t ^ 2 + 1) • (1 : Matrix n n ℝ)))) := by
  apply contDiff_inverse_sqrt_comp
  · fun_prop
  · intro t
    exact Matrix.PosDef.one.smul (by positivity)

theorem empty_rank_smooth :
    ContDiff ℝ ∞ (fun t : ℝ =>
      CFC.sqrt ((t ^ 2 + 1) • (1 : Matrix (Fin 0) (Fin 0) ℝ))) :=
  polynomial_family_smooth

theorem empty_rank_inverse_smooth :
    ContDiff ℝ ∞ (fun t : ℝ =>
      Ring.inverse (CFC.sqrt ((t ^ 2 + 1) • (1 : Matrix (Fin 0) (Fin 0) ℝ)))) :=
  polynomial_inverse_family_smooth

-- Parameter subsets need neither openness nor unique differentiability.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Matrix n n ℝ} {s : Set E}
    (hf : ContDiffOn ℝ ∞ f s) (hp : ∀ x ∈ s, (f x).PosDef) :
    ContDiffOn ℝ ∞ (fun x => CFC.sqrt (f x)) s ∧
    ContDiffOn ℝ ∞ (fun x => Ring.inverse (CFC.sqrt (f x))) s :=
  ⟨contDiffOn_sqrt_comp hf hp, contDiffOn_inverse_sqrt_comp hf hp⟩

-- The delivered inverse actually solves the full Sylvester equation.
example {S : Matrix n n ℝ} (hS : S.PosDef) (K : Matrix n n ℝ) :
    S * (sylvesterEquiv hS).symm K + (sylvesterEquiv hS).symm K * S = K := by
  exact (sylvesterEquiv hS).apply_symm_apply K

example (K : Matrix (Fin 0) (Fin 0) ℝ) :
    (sylvesterEquiv (Matrix.PosDef.one : (1 : Matrix (Fin 0) (Fin 0) ℝ).PosDef))
      ((sylvesterEquiv Matrix.PosDef.one).symm K) = K :=
  (sylvesterEquiv Matrix.PosDef.one).apply_symm_apply K

end NormalizationSqrtConsumer
#eval IO.println "NORMALIZATION_SQRT_CONSUMERS_COMPLETE"
