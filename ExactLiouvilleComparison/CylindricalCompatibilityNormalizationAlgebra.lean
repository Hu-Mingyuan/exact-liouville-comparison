import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraStatement
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Tactic.NoncommRing

noncomputable section
open Matrix
open scoped MatrixOrder
namespace ExactLiouvilleComparison.NormalizationAlgebra
variable {n : ℕ}

lemma mul_inv (A : Mat n) (hA : IsUnit A) : A * A⁻¹ = 1 :=
  A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA)

lemma inv_mul (A : Mat n) (hA : IsUnit A) : A⁻¹ * A = 1 :=
  A.nonsing_inv_mul (A.isUnit_iff_isUnit_det.mp hA)

lemma inv_unit {A : Mat n} (hA : IsUnit A) : IsUnit A⁻¹ :=
  Matrix.isUnit_nonsing_inv_iff.mpr hA

lemma posDef_transpose {G : Mat n} (hG : G.PosDef) : G.transpose = G := by
  simpa using hG.isHermitian.eq

lemma sqrt_posDef {G : Mat n} (hG : G.PosDef) : (CFC.sqrt G).PosDef :=
  Matrix.IsStrictlyPositive.posDef (hG.isStrictlyPositive.sqrt G)

lemma root_posDef {G : Mat n} (hG : G.PosDef) : (metricRoot G).PosDef :=
  sqrt_posDef hG

lemma root_sq {G : Mat n} (hG : G.PosDef) : metricRoot G * metricRoot G = G :=
  CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg

lemma form_pull (P W : Mat n) (v w : Vec n) :
    form (pull P W) v w = form W (P *ᵥ v) (P *ᵥ w) := by
  simp only [form, Matrix.toBilin'_apply', pull, ← mulVec_mulVec]
  rw [dotProduct_transpose_mulVec, dotProduct_comm]

lemma form_skew {W : Mat n} (hW : W.transpose = -W) (v w : Vec n) :
    form W v w = -form W w v := by
  have h := dotProduct_transpose_mulVec W w v
  rw [hW] at h
  simpa [form, Matrix.toBilin'_apply', neg_mulVec, dotProduct_neg] using h.symm

lemma form_isAlt {W : Mat n} (hW : W.transpose = -W) : (form W).IsAlt := by
  intro v
  have h := form_skew hW v v
  linarith

lemma form_nondegenerate_iff (W : Mat n) : (form W).Nondegenerate ↔ IsUnit W := by
  rw [LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero, W.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

lemma pull_posDef {G : Mat n} (hG : G.PosDef) {P : Mat n} (hP : IsUnit P) :
    (pull P G).PosDef := by
  simpa [pull] using hG.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.mpr hP)

lemma pull_skew {W : Mat n} (hW : W.transpose = -W) (P : Mat n) :
    (pull P W).transpose = -pull P W := by
  simp [pull, transpose_mul, hW, mul_assoc]

lemma pull_unit {W P : Mat n} (hW : IsUnit W) (hP : IsUnit P) :
    IsUnit (pull P W) := by
  have hPt : IsUnit P.transpose := by
    rw [P.transpose.isUnit_iff_isUnit_det, det_transpose]
    exact P.isUnit_iff_isUnit_det.mp hP
  exact (hPt.mul hW).mul hP

lemma skew_transpose {G W : Mat n} (hG : G.PosDef) (hW : W.transpose = -W) :
    (skew G W).transpose = -skew G W := by
  have hB := posDef_transpose (root_posDef hG).inv
  simp [skew, transpose_mul, hB, hW, mul_assoc]

lemma skew_unit {G W : Mat n} (hG : G.PosDef) (hW : IsUnit W) :
    IsUnit (skew G W) :=
  ((inv_unit (root_posDef hG).isUnit).neg.mul hW).mul
    (inv_unit (root_posDef hG).isUnit)

lemma neg_sq_posDef {K : Mat n} (hK : K.transpose = -K) (hKu : IsUnit K) :
    (-(K * K)).PosDef := by
  simpa [hK] using Matrix.PosDef.conjTranspose_mul_self K
    (mulVec_injective_iff_isUnit.mpr hKu)

lemma polarRoot_posDef {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) : (polarRoot G W).PosDef :=
  sqrt_posDef (neg_sq_posDef (skew_transpose hG hW) (skew_unit hG hWu))

lemma polarRoot_sq {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) :
    polarRoot G W * polarRoot G W = -(skew G W * skew G W) :=
  CFC.sqrt_mul_sqrt_self _
    (neg_sq_posDef (skew_transpose hG hW) (skew_unit hG hWu)).posSemidef.nonneg

lemma polarRoot_commute (G W : Mat n) : Commute (polarRoot G W) (skew G W) := by
  apply Commute.cfcₙ_nnreal (f := NNReal.sqrt)
  show -(skew G W * skew G W) * skew G W = skew G W * -(skew G W * skew G W)
  noncomm_ring

lemma commute_inv_right {A B : Mat n} (h : Commute A B) (hB : IsUnit B) :
    Commute A B⁻¹ := by
  change A * B⁻¹ = B⁻¹ * A
  calc
    A * B⁻¹ = (B⁻¹ * B) * A * B⁻¹ := by rw [inv_mul B hB, one_mul]
    _ = B⁻¹ * (A * B) * B⁻¹ := by rw [mul_assoc B⁻¹, h.eq]
    _ = B⁻¹ * A := by simp only [mul_assoc, mul_inv B hB, mul_one]

lemma mul_inv_cancel_right (A B : Mat n) (hB : IsUnit B) : A * B * B⁻¹ = A := by
  rw [mul_assoc, mul_inv B hB, mul_one]

lemma inv_mul_cancel_right (A B : Mat n) (hB : IsUnit B) : A * B⁻¹ * B = A := by
  rw [mul_assoc, inv_mul B hB, mul_one]

/-- Algebra of the actual polar factor, with square-root identities as explicit
internal lemma hypotheses, discharged by CFC in the public normalization theorem. -/
lemma polar_factor_sq {K Q : Mat n} (hQ : Q * Q = -(K * K))
    (hQu : IsUnit Q) (hcomm : Commute K Q) :
    (K * Q⁻¹) * (K * Q⁻¹) = -1 := by
  have hc := commute_inv_right hcomm hQu
  calc
    (K * Q⁻¹) * (K * Q⁻¹) = K * (Q⁻¹ * K) * Q⁻¹ := by noncomm_ring
    _ = (K * K) * Q⁻¹ * Q⁻¹ := by rw [← hc.eq]; noncomm_ring
    _ = -(Q * Q) * Q⁻¹ * Q⁻¹ := by rw [hQ, neg_neg]
    _ = -1 := by simp only [neg_mul, mul_inv_cancel_right _ Q hQu, mul_inv Q hQu]

lemma polar_factor_metric {K Q : Mat n} (hQ : Q * Q = -(K * K))
    (hQu : IsUnit Q) : -K * (K * Q⁻¹) = Q := by
  rw [← mul_assoc, neg_mul, ← hQ, mul_inv_cancel_right _ Q hQu]

lemma form_eq_whitened {G W : Mat n} (hG : G.PosDef) :
    W = -(metricRoot G * skew G W * metricRoot G) := by
  have hH := (root_posDef hG).isUnit
  simp only [skew, mul_neg, neg_mul, neg_neg]
  rw [← mul_assoc, ← mul_assoc, mul_inv _ hH, one_mul,
    inv_mul_cancel_right _ _ hH]

lemma normalize_sq {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) :
    normalize G W * normalize G W = -1 := by
  have hH := (root_posDef hG).isUnit
  have hQ := (polarRoot_posDef hG hW hWu).isUnit
  have hL := polar_factor_sq (polarRoot_sq hG hW hWu) hQ
    (polarRoot_commute G W).symm
  let H := metricRoot G
  let L := skew G W * (polarRoot G W)⁻¹
  change (H⁻¹ * skew G W * (polarRoot G W)⁻¹ * H) *
    (H⁻¹ * skew G W * (polarRoot G W)⁻¹ * H) = -1
  calc
    _ = H⁻¹ * L * (H * H⁻¹) * L * H := by dsimp [L]; noncomm_ring
    _ = H⁻¹ * (L * L) * H := by rw [mul_inv H hH]; noncomm_ring
    _ = -1 := by rw [hL]; simp [inv_mul H hH]

lemma normalize_metric {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) :
    W * normalize G W = metricRoot G * polarRoot G W * metricRoot G := by
  have hH := (root_posDef hG).isUnit
  have hQ := (polarRoot_posDef hG hW hWu).isUnit
  have hL := polar_factor_metric (polarRoot_sq hG hW hWu) hQ
  calc
    W * normalize G W = -(metricRoot G * skew G W * metricRoot G) *
        ((metricRoot G)⁻¹ * skew G W * (polarRoot G W)⁻¹ * metricRoot G) := by
      rw [← form_eq_whitened hG]; rfl
    _ = metricRoot G * (-skew G W) * (metricRoot G * (metricRoot G)⁻¹) *
        (skew G W * (polarRoot G W)⁻¹) * metricRoot G := by noncomm_ring
    _ = metricRoot G * (-skew G W * (skew G W * (polarRoot G W)⁻¹)) *
        metricRoot G := by rw [mul_inv _ hH]; noncomm_ring
    _ = _ := by rw [hL]

lemma normalize_metric_posDef {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) : (W * normalize G W).PosDef := by
  rw [normalize_metric hG hW hWu]
  have h := pull_posDef (polarRoot_posDef hG hW hWu) (root_posDef hG).isUnit
  simpa [pull, posDef_transpose (root_posDef hG)] using h

/-- Compatibility follows from the complex square and the positive induced metric. -/
lemma compatible_of_metric {W J : Mat n} (hW : W.transpose = -W)
    (hJ : J * J = -1) (hG : (W * J).PosDef) : Compatible W J := by
  refine ⟨hJ, ?_, ?_⟩
  · have ht := posDef_transpose hG
    rw [transpose_mul, hW, mul_neg] at ht
    have ht' : J.transpose * W = -(W * J) := by rw [← ht, neg_neg]
    rw [ht', neg_mul, mul_assoc, hJ, mul_neg, mul_one, neg_neg]
  · intro v hv
    have hp := hG.dotProduct_mulVec_pos hv
    simpa only [star_trivial, form, Matrix.toBilin'_apply', mulVec_mulVec] using hp

/-- Actual compatibility of the explicit real-matrix normalization. -/
theorem normalize_compatible {G W : Mat n} (hG : G.PosDef)
    (hW : W.transpose = -W) (hWu : IsUnit W) : Compatible W (normalize G W) :=
  compatible_of_metric hW (normalize_sq hG hW hWu) (normalize_metric_posDef hG hW hWu)

end ExactLiouvilleComparison.NormalizationAlgebra
