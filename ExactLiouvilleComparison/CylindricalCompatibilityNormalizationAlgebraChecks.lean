import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraNative
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
open Matrix
open scoped MatrixOrder
namespace ExactLiouvilleComparison.NormalizationAlgebra

/-- The canonical plane has the positive sign prescribed by the manuscript. -/
def planeForm : Mat 2 := !![0, 1; -1, 0]
def planeComplex : Mat 2 := !![0, -1; 1, 0]

lemma planeComplex_sq : planeComplex * planeComplex = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [planeComplex, Matrix.mul_apply, Fin.sum_univ_two]

lemma plane_metric : (1 : Mat 2) = planeForm * planeComplex := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [planeForm, planeComplex, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete consumer of the literal CFC formula; no chosen normalizer witness. -/
theorem normalize_plane : normalize 1 planeForm = planeComplex :=
  normalize_recovery Matrix.PosDef.one planeComplex_sq plane_metric

/-- Recovery also holds literally for the native continuous linear endomorphism. -/
theorem normalize_native_recovery {n : ℕ} {G W J : Mat n} (hG : G.PosDef)
    (hJ : Compatible W J) (hmetric : G = W * J) :
    endomorphism (normalize G W) = endomorphism J := by
  rw [normalize_recovery hG hJ.1 hmetric]

/-- Zero-rank input satisfies every admissibility hypothesis, including invertibility. -/
theorem zero_rank_admissible (G W : Mat 0) :
    G.PosDef ∧ W.transpose = -W ∧ IsUnit W := by
  have hG : G = 1 := Subsingleton.elim _ _
  have hW : W = 1 := Subsingleton.elim _ _
  exact ⟨hG ▸ Matrix.PosDef.one, Subsingleton.elim _ _, hW ▸ isUnit_one⟩

theorem zero_rank_compatible (G W : Mat 0) : Compatible W (normalize G W) :=
  normalize_compatible (zero_rank_admissible G W).1
    (zero_rank_admissible G W).2.1 (zero_rank_admissible G W).2.2

-- These are proofs of the reviewed targets, not new assumptions.
example : NormalizationContract := normalizationContract
example : RecoveryContract := recoveryContract
example : NaturalityContract := naturalityContract

end ExactLiouvilleComparison.NormalizationAlgebra
