import ExactLiouvilleComparison.CylindricalCompatibilityStatement
import FsFltz.Geometry.CompatibleComplexPath

/-! The linear algebra of the prescribed end, on the actual boundary tangent
fibers. Identification with the pulled-back completion form is separate. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactData

variable {d : ℕ} {D : LiouvilleDomain d} (P : ContactData D)

/-- The actual boundary one-form as a continuous linear functional. -/
def alphaLinear (y : D.domain.boundary.Point) : D.domain.boundary.Tangent y →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ (D.domain.boundary.Tangent y) ℝ
    (0 : Fin 1)).symm (alpha D y)

@[simp] theorem alphaLinear_apply (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    alphaLinear (D := D) y v = evalOne (alpha D) y v := rfl

/-- The full cylindrical formula in product tangent coordinates. -/
def endJ (y : D.domain.boundary.Point) :
    (D.domain.boundary.Tangent y × ℝ) →L[ℝ] (D.domain.boundary.Tangent y × ℝ) :=
  ((P.J y).comp (ContinuousLinearMap.fst ℝ _ _) +
    (ContinuousLinearMap.snd ℝ _ _).smulRight (P.reeb y)).prod
      (-(alphaLinear (D := D) y).comp
        (ContinuousLinearMap.fst ℝ (D.domain.boundary.Tangent y) ℝ))

@[simp] theorem endJ_apply (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) (s : ℝ) :
    P.endJ y (v, s) =
      (P.J y v + s • P.reeb y, -evalOne (alpha D) y v) := rfl

/-- No nonemptiness or positive-dimension premise is used in the square law. -/
theorem endJ_square (y : D.domain.boundary.Point)
    (z : D.domain.boundary.Tangent y × ℝ) :
    P.endJ y (P.endJ y z) = -z := by
  rcases z with ⟨v, s⟩
  simp only [endJ_apply, map_add, map_smul, P.annihilate_reeb, smul_zero,
    add_zero, P.square, evalOne_add, evalOne_smul, P.horizontal, P.normalized,
    zero_add, mul_one, neg_smul, Prod.neg_mk]
  congr 1
  abel

theorem endJ_time (y : D.domain.boundary.Point) :
    P.endJ y (0, 1) = (P.reeb y, 0) := by
  have hzero : evalOne (alpha D) y 0 = 0 := (alphaLinear (D := D) y).map_zero
  simp [endJ_apply, hzero]

theorem endJ_reeb (y : D.domain.boundary.Point) :
    P.endJ y (P.reeb y, 0) = (0, -1) := by
  simp [endJ_apply, P.annihilate_reeb, P.normalized]

/-- The explicit bilinear expression dt ∧ alpha + d alpha. The exponential
factor is included in `endPairing`; no replacement differential is postulated. -/
def endPairing (y : D.domain.boundary.Point) (t : ℝ)
    (z w : D.domain.boundary.Tangent y × ℝ) : ℝ :=
  Real.exp t * (evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y z.1 w.1 +
    z.2 * evalOne (alpha D) y w.1 - w.2 * evalOne (alpha D) y z.1)

theorem differential_reeb_right (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v (P.reeb y) = 0 := by
  rw [evalTwo_swap, P.kernel, neg_zero]

theorem endPairing_invariant (y : D.domain.boundary.Point) (t : ℝ)
    (z w : D.domain.boundary.Tangent y × ℝ) :
    endPairing (D := D) y t (P.endJ y z) (P.endJ y w) = endPairing y t z w := by
  rcases z with ⟨v, s⟩
  rcases w with ⟨w, u⟩
  simp only [endPairing, endJ_apply, evalTwo_add_left, evalTwo_add_right,
    evalTwo_smul_left, evalTwo_smul_right, P.invariant, P.kernel,
    P.differential_reeb_right, mul_zero, add_zero, evalOne_add, evalOne_smul,
    P.horizontal, P.normalized, mul_one, zero_add]
  ring

/-- The positive energy expression has the manuscript's positive Reeb sign. -/
theorem endPairing_energy (y : D.domain.boundary.Point) (t : ℝ)
    (v : D.domain.boundary.Tangent y) (s : ℝ) :
    endPairing y t (v, s) (P.endJ y (v, s)) =
      Real.exp t * (evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y
        v (P.J y v) + s ^ 2 + (evalOne (alpha D) y v) ^ 2) := by
  simp only [endPairing, endJ_apply, evalTwo_add_right, evalTwo_smul_right,
    P.differential_reeb_right, mul_zero, add_zero, evalOne_add, evalOne_smul,
    P.horizontal, P.normalized, mul_one, zero_add]
  ring

/-- Removing the Reeb component does not change the contact energy. -/
theorem horizontal_energy (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y
      (v - evalOne (alpha D) y v • P.reeb y)
      (P.J y (v - evalOne (alpha D) y v • P.reeb y)) =
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v (P.J y v) := by
  simp only [map_sub, map_smul, P.annihilate_reeb, smul_zero, sub_zero,
    evalTwo_sub_left, evalTwo_smul_left, P.kernel, mul_zero, sub_zero]

theorem contact_energy_nonneg (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    0 ≤ evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v (P.J y v) := by
  let v₀ := v - evalOne (alpha D) y v • P.reeb y
  have hh : evalOne (alpha D) y v₀ = 0 := by
    simp [v₀, evalOne_sub, evalOne_smul, P.normalized]
  rw [← P.horizontal_energy]
  change 0 ≤ evalTwo _ y v₀ (P.J y v₀)
  by_cases hzero : v₀ = 0
  · have he := evalTwo_smul_left (D.domain.boundary.exteriorDerivative (alpha D))
      y 0 (0 : D.domain.boundary.Tangent y) (P.J y 0)
    simpa [hzero] using he.ge
  · exact (P.positive y v₀ hh hzero).le

/-- Strict positivity on every nonzero product tangent, including rank-zero
contact distributions. -/
theorem endPairing_positive (y : D.domain.boundary.Point) (t : ℝ)
    (z : D.domain.boundary.Tangent y × ℝ) (hz : z ≠ 0) :
    0 < endPairing y t z (P.endJ y z) := by
  rcases z with ⟨v, s⟩
  rw [P.endPairing_energy]
  apply mul_pos (Real.exp_pos t)
  have hn := P.contact_energy_nonneg y v
  by_cases hs : s = 0
  · subst s
    by_cases ha : evalOne (alpha D) y v = 0
    · have hv : v ≠ 0 := by
        intro hv
        exact hz (by simp [hv])
      have hp := P.positive y v ha hv
      nlinarith [sq_nonneg (evalOne (alpha D) y v)]
    · nlinarith [sq_pos_of_ne_zero ha]
  · nlinarith [sq_pos_of_ne_zero hs, sq_nonneg (evalOne (alpha D) y v)]

end ExactLiouvilleComparison.CylindricalCompatibility.ContactData
