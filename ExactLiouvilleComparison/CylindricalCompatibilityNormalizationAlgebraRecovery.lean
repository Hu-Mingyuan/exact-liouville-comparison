import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebra

noncomputable section
open Matrix
open scoped MatrixOrder
namespace ExactLiouvilleComparison.NormalizationAlgebra
variable {n : ℕ}

/-- Recovery needs only the complex square and the metric identity. -/
theorem normalize_recovery {G W J : Mat n} (hG : G.PosDef)
    (hJ : J * J = -1) (hmetric : G = W * J) : normalize G W = J := by
  have hH := (root_posDef hG).isUnit
  have hW : W = -(G * J) := by
    rw [hmetric, mul_assoc, hJ, mul_neg, mul_one, neg_neg]
  have hK : skew G W = metricRoot G * J * (metricRoot G)⁻¹ := by
    calc
      _ = (metricRoot G)⁻¹ * G * J * (metricRoot G)⁻¹ := by
        rw [skew, hW]; noncomm_ring
      _ = (metricRoot G)⁻¹ * (metricRoot G * metricRoot G) * J *
          (metricRoot G)⁻¹ := by rw [root_sq hG]
      _ = _ := by simp only [← mul_assoc, inv_mul _ hH, one_mul]
  have hKK : skew G W * skew G W = -1 := by
    rw [hK]
    calc
      _ = metricRoot G * J * ((metricRoot G)⁻¹ * metricRoot G) *
        J * (metricRoot G)⁻¹ := by noncomm_ring
      _ = metricRoot G * (J * J) * (metricRoot G)⁻¹ := by
        rw [inv_mul _ hH]; noncomm_ring
      _ = -1 := by rw [hJ]; simp [mul_inv _ hH]
  have hQ : polarRoot G W = 1 := by
    simp only [polarRoot, hKK, neg_neg, CFC.sqrt_one]
  simp only [normalize, hQ, inv_one, mul_one, hK]
  simp only [← mul_assoc, inv_mul _ hH, one_mul, inv_mul_cancel_right _ _ hH]

/-- The reviewed normalization obligation is proved in every finite rank. -/
theorem normalizationContract : NormalizationContract := by
  intro n G W hG hW hWu
  exact normalize_compatible hG hW hWu

/-- The reviewed recovery obligation, without any extra assumptions. -/
theorem recoveryContract : RecoveryContract := by
  intro n G W J hG _ _ hJ hmetric
  exact normalize_recovery hG hJ.1 hmetric

end ExactLiouvilleComparison.NormalizationAlgebra
