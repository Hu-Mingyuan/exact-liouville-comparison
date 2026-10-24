import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraRecovery

noncomputable section
open Matrix
open scoped MatrixOrder
namespace ExactLiouvilleComparison.NormalizationAlgebra
variable {n : ℕ}

lemma pull_neg (U A : Mat n) : pull U (-A) = -pull U A := by simp [pull]

lemma pull_mul_orthogonal {U : Mat n} (hU : U * U.transpose = 1) (A B : Mat n) :
    pull U A * pull U B = pull U (A * B) := by
  unfold pull
  calc
    _ = U.transpose * A * (U * U.transpose) * B * U := by noncomm_ring
    _ = _ := by rw [hU]; noncomm_ring

lemma pull_one_orthogonal {U : Mat n} (hU : U.transpose * U = 1) : pull U 1 = 1 := by
  simpa [pull] using hU

/-- Square-root transport is proved only for orthogonal whitening transitions. -/
lemma sqrt_pull_orthogonal {U A : Mat n} (hU : U.transpose * U = 1) :
    CFC.sqrt (pull U A) = pull U (CFC.sqrt A) := by
  by_cases hA : 0 ≤ A
  · apply CFC.sqrt_unique
    · rw [pull_mul_orthogonal (mul_eq_one_comm.mpr hU), CFC.sqrt_mul_sqrt_self A hA]
    · exact (by simpa [pull] using
        (CFC.sqrt_nonneg A).posSemidef.conjTranspose_mul_mul_same U :
        (pull U (CFC.sqrt A)).PosSemidef).nonneg
  · have hAu : ¬0 ≤ pull U A := by
      intro h
      have hh := h.posSemidef.conjTranspose_mul_mul_same U.transpose
      have hUU := mul_eq_one_comm.mpr hU
      have heq : pull U.transpose (pull U A) = A := by
        simp only [pull, transpose_transpose]
        calc
          _ = (U * U.transpose) * A * (U * U.transpose) := by noncomm_ring
          _ = A := by rw [hUU]; simp
      apply hA
      have : (pull U.transpose (pull U A)).PosSemidef := by simpa [pull] using hh
      rw [heq] at this
      exact this.nonneg
    rw [CFC.sqrt_of_not_nonneg hAu, CFC.sqrt_of_not_nonneg hA]
    simp [pull]

lemma inv_pull_orthogonal {U A : Mat n} (hU : U.transpose * U = 1)
    (hA : IsUnit A) : (pull U A)⁻¹ = pull U A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [pull_mul_orthogonal (mul_eq_one_comm.mpr hU), mul_inv A hA,
    pull_one_orthogonal hU]

/-- Arbitrary coordinate changes induce orthogonal changes between whitened metrics. -/
lemma whitening_orthogonal {G P : Mat n} (hG : G.PosDef) (hP : IsUnit P) :
    let U := metricRoot G * P * (metricRoot (pull P G))⁻¹
    U.transpose * U = 1 := by
  have hG' := pull_posDef hG hP
  have hH' := (root_posDef hG').isUnit
  dsimp
  rw [transpose_mul, transpose_mul, posDef_transpose (root_posDef hG),
    posDef_transpose (root_posDef hG').inv]
  calc
    _ = (metricRoot (pull P G))⁻¹ *
        (P.transpose * (metricRoot G * metricRoot G) * P) *
        (metricRoot (pull P G))⁻¹ := by noncomm_ring
    _ = (metricRoot (pull P G))⁻¹ * (pull P G) *
        (metricRoot (pull P G))⁻¹ := by rw [root_sq hG]; rfl
    _ = (metricRoot (pull P G))⁻¹ *
        (metricRoot (pull P G) * metricRoot (pull P G)) *
        (metricRoot (pull P G))⁻¹ := by rw [root_sq hG']
    _ = 1 := by
      simp only [← mul_assoc, inv_mul _ hH', one_mul, mul_inv _ hH']

lemma skew_pull {G W P : Mat n} (hG : G.PosDef) (hP : IsUnit P) :
    let U := metricRoot G * P * (metricRoot (pull P G))⁻¹
    skew (pull P G) (pull P W) = pull U (skew G W) := by
  have hG' := pull_posDef hG hP
  have heq : metricRoot G * skew G W * metricRoot G = -W := by
    simpa only [neg_neg] using congrArg Neg.neg (form_eq_whitened (W := W) hG).symm
  dsimp
  symm
  have hB' : ((metricRoot (P.transpose * G * P))⁻¹).transpose =
      (metricRoot (P.transpose * G * P))⁻¹ := posDef_transpose (root_posDef hG').inv
  unfold pull
  rw [transpose_mul, transpose_mul, posDef_transpose (root_posDef hG),
    hB']
  calc
    _ = (metricRoot (P.transpose * G * P))⁻¹ * P.transpose *
        (metricRoot G * skew G W * metricRoot G) * P *
        (metricRoot (P.transpose * G * P))⁻¹ := by noncomm_ring
    _ = _ := by rw [heq]; unfold skew; noncomm_ring

lemma polarRoot_pull {G W P : Mat n} (hG : G.PosDef) (hP : IsUnit P) :
    let U := metricRoot G * P * (metricRoot (pull P G))⁻¹
    polarRoot (pull P G) (pull P W) = pull U (polarRoot G W) := by
  let U := metricRoot G * P * (metricRoot (pull P G))⁻¹
  have hU : U.transpose * U = 1 := whitening_orthogonal hG hP
  change CFC.sqrt (-(skew (pull P G) (pull P W) * skew (pull P G) (pull P W))) =
    pull U (CFC.sqrt (-(skew G W * skew G W)))
  rw [skew_pull hG hP, pull_mul_orthogonal (mul_eq_one_comm.mpr hU), ← pull_neg,
    sqrt_pull_orthogonal hU]

/-- The explicit formula is equivariant under every invertible coordinate change. -/
theorem normalize_naturality {G W P : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) (hP : IsUnit P) :
    normalize (pull P G) (pull P W) = P⁻¹ * normalize G W * P := by
  let H := metricRoot G
  let H' := metricRoot (pull P G)
  let U := H * P * H'⁻¹
  let L := skew G W * (polarRoot G W)⁻¹
  have hH : IsUnit H := (root_posDef hG).isUnit
  have hH' : IsUnit H' := (root_posDef (pull_posDef hG hP)).isUnit
  have hU : U.transpose * U = 1 := whitening_orthogonal hG hP
  have hUU : U * U.transpose = 1 := mul_eq_one_comm.mpr hU
  have hUH : U * H' = H * P := by
    dsimp [U]; rw [inv_mul_cancel_right _ _ hH']
  have hBU : H'⁻¹ * U.transpose = P⁻¹ * H⁻¹ := by
    have hleft : (H'⁻¹ * U.transpose) * (H * P) = 1 := by
      rw [← hUH]
      calc
        _ = H'⁻¹ * (U.transpose * U) * H' := by noncomm_ring
        _ = 1 := by rw [hU, mul_one, inv_mul _ hH']
    have hright : (H * P) * (P⁻¹ * H⁻¹) = 1 := by
      calc
        _ = H * (P * P⁻¹) * H⁻¹ := by noncomm_ring
        _ = 1 := by rw [mul_inv _ hP, mul_one, mul_inv _ hH]
    exact Matrix.right_inv_eq_left_inv hright hleft |>.symm
  have hL : skew (pull P G) (pull P W) * (polarRoot (pull P G) (pull P W))⁻¹ =
      pull U L := by
    rw [skew_pull hG hP, polarRoot_pull hG hP,
      inv_pull_orthogonal hU (polarRoot_posDef hG hW hWu).isUnit,
      pull_mul_orthogonal hUU]
  calc
    normalize (pull P G) (pull P W) = H'⁻¹ *
        (skew (pull P G) (pull P W) * (polarRoot (pull P G) (pull P W))⁻¹) * H' := by
      unfold normalize; noncomm_ring
    _ = H'⁻¹ * (pull U L) * H' := by rw [hL]
    _ = (H'⁻¹ * U.transpose) * L * (U * H') := by unfold pull; noncomm_ring
    _ = (P⁻¹ * H⁻¹) * L * (H * P) := by rw [hBU, hUH]
    _ = P⁻¹ * normalize G W * P := by dsimp [normalize, H, L]; noncomm_ring

/-- The reviewed naturality obligation is proved with no restriction on `P` beyond invertibility. -/
theorem naturalityContract : NaturalityContract := by
  intro n G W P hG hW hWu hP
  exact normalize_naturality hG hW hWu hP

end ExactLiouvilleComparison.NormalizationAlgebra
