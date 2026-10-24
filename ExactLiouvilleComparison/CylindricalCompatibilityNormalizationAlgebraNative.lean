import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraNaturality

noncomputable section
open Matrix
open scoped MatrixOrder
namespace ExactLiouvilleComparison.NormalizationAlgebra
variable {n : ℕ}

/-- The same matrix as a native continuous linear endomorphism of coordinate space. -/
def endomorphism (J : Mat n) : Vec n →L[ℝ] Vec n :=
  LinearMap.toContinuousLinearMap J.mulVecLin

@[simp] lemma endomorphism_apply (J : Mat n) (v : Vec n) :
    endomorphism J v = J *ᵥ v := rfl

/-- The native continuous bilinear form, with no change to its values. -/
def continuousForm (W : Mat n) : Vec n →L[ℝ] Vec n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Vec n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Vec n →L[ℝ] ℝ)).toLinearMap.comp
      (form W))

@[simp] lemma continuousForm_apply (W : Mat n) (v w : Vec n) :
    continuousForm W v w = form W v w := rfl

lemma form_left (A G : Mat n) (v w : Vec n) :
    form G (A *ᵥ v) w = form (A.transpose * G) v w := by
  simp only [form, Matrix.toBilin'_apply', ← mulVec_mulVec]
  rw [dotProduct_transpose_mulVec, dotProduct_comm]

/-- Sign bridge for the defining equation `g (A v) w = omega v w`. -/
lemma associated_operator_equation {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (v w : Vec n) :
    form G ((-G⁻¹ * W) *ᵥ v) w = form W v w := by
  rw [form_left]
  congr 1
  rw [transpose_mul, transpose_neg, posDef_transpose hG.inv, hW, neg_mul_neg,
    inv_mul_cancel_right _ _ hG.isUnit]

/-- Bridge between congruence whitening and the metric-associated operator. -/
lemma skew_eq_whitened_operator {G W : Mat n} (hG : G.PosDef) :
    skew G W = metricRoot G * (-G⁻¹ * W) * (metricRoot G)⁻¹ := by
  have hH := (root_posDef hG).isUnit
  have hB : G⁻¹ = (metricRoot G)⁻¹ * (metricRoot G)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    calc
      _ = (metricRoot G * metricRoot G) *
        ((metricRoot G)⁻¹ * (metricRoot G)⁻¹) := by rw [root_sq hG]
      _ = 1 := by simp only [← mul_assoc, mul_inv_cancel_right _ _ hH, mul_inv _ hH]
  rw [hB]
  unfold skew
  simp only [mul_neg, neg_mul, ← mul_assoc, mul_inv _ hH, one_mul]

/-- Native CLM consumer of the constructed compatible complex structure. -/
theorem normalize_native {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) :
    let J := endomorphism (normalize G W)
    (∀ v, J (J v) = -v) ∧
    (∀ v w, continuousForm W (J v) (J w) = continuousForm W v w) ∧
    (∀ v, v ≠ 0 → 0 < continuousForm W v (J v)) := by
  have hc := normalize_compatible hG hW hWu
  dsimp only
  refine ⟨?_, ?_, hc.2.2⟩
  · intro v
    simpa only [endomorphism_apply, mulVec_mulVec, hc.1, neg_mulVec, one_mulVec]
  · intro v w
    change form W (normalize G W *ᵥ v) (normalize G W *ᵥ w) = form W v w
    rw [← form_pull]
    change form ((normalize G W).transpose * W * normalize G W) v w = _
    rw [hc.2.1]

/-- Native evaluation of the arbitrary coordinate-change law. -/
theorem normalize_native_naturality {G W P : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) (hP : IsUnit P) (v : Vec n) :
    endomorphism (normalize (pull P G) (pull P W)) v =
      endomorphism P⁻¹ (endomorphism (normalize G W) (endomorphism P v)) := by
  simp only [endomorphism_apply, mulVec_mulVec, normalize_naturality hG hW hWu hP,
    mul_assoc]

/-- Explicit zero-rank consumer, preserving the unique endomorphism. -/
theorem normalize_rank_zero (G W : Mat 0) : normalize G W = 1 :=
  Subsingleton.elim _ _

end ExactLiouvilleComparison.NormalizationAlgebra
