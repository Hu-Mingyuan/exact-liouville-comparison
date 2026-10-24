import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Analytic contracts only. These propositions are not proof certificates. -/
noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff

namespace ExactLiouvilleComparison.NormalizationSqrt

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The Sylvester operator at every positive-definite real matrix is an actual
continuous linear equivalence of the full matrix space. -/
def SylvesterContract : Prop :=
  ∀ S : Matrix n n ℝ, S.PosDef →
    ∃ L : Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ, ∀ H, L H = S * H + H * S

/-- Smoothness relative to the positive-definite cone, with no nonempty-index assumption. -/
def RelativeSqrtContract : Prop :=
  ContDiffOn ℝ ∞ (CFC.sqrt : Matrix n n ℝ → Matrix n n ℝ) {A | A.PosDef}

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local coefficient families may be smooth only within a set. -/
def SqrtCompositionContract : Prop :=
  ∀ (f : E → Matrix n n ℝ) (s : Set E), ContDiffOn ℝ ∞ f s →
    (∀ x ∈ s, (f x).PosDef) → ContDiffOn ℝ ∞ (fun x => CFC.sqrt (f x)) s

/-- The inverse uses the native total ring inverse, at matrices proved to be units. -/
def InverseSqrtCompositionContract : Prop :=
  ∀ (f : E → Matrix n n ℝ) (s : Set E), ContDiffOn ℝ ∞ f s →
    (∀ x ∈ s, (f x).PosDef) →
    ContDiffOn ℝ ∞ (fun x => Ring.inverse (CFC.sqrt (f x))) s

end ExactLiouvilleComparison.NormalizationSqrt
