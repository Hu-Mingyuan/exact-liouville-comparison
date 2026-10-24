import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationSqrtStatement

noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff Topology
open Matrix

namespace ExactLiouvilleComparison.NormalizationSqrt
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The derivative of squaring on the full real matrix space. -/
def sylvester (S : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  ContinuousLinearMap.mul ℝ _ S + (ContinuousLinearMap.mul ℝ _).flip S

@[simp] theorem sylvester_apply (S H : Matrix n n ℝ) :
    sylvester S H = S * H + H * S := rfl

/-- In spectral coordinates each entry is multiplied by a positive eigenvalue sum. -/
theorem sylvester_injective {S : Matrix n n ℝ} (hS : S.PosDef) :
    Function.Injective (sylvester S) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro H hH
  let e := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) (star hS.isHermitian.eigenvectorUnitary)
  have heS : e S = diagonal hS.isHermitian.eigenvalues := by
    simpa [e, Function.comp_def] using hS.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have heH := congrArg e hH
  change e (S * H + H * S) = e 0 at heH
  rw [map_add, map_mul, map_mul, map_zero, heS] at heH
  have hz : e H = 0 := by
    ext i j
    have hij := congrArg (fun A : Matrix n n ℝ => A i j) heH
    simp only [Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.zero_apply] at hij
    have hp : 0 < hS.isHermitian.eigenvalues i + hS.isHermitian.eigenvalues j :=
      add_pos (hS.eigenvalues_pos i) (hS.eigenvalues_pos j)
    have hm : (hS.isHermitian.eigenvalues i + hS.isHermitian.eigenvalues j) * e H i j = 0 := by
      nlinarith [hij]
    exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hp)
  exact e.injective (hz.trans (map_zero e).symm)

/-- The actual Sylvester continuous linear equivalence, without a nonempty-index restriction. -/
def sylvesterEquiv {S : Matrix n n ℝ} (hS : S.PosDef) :
    Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ :=
  (LinearEquiv.ofInjectiveEndo (sylvester S).toLinearMap
    (sylvester_injective hS)).toContinuousLinearEquiv

@[simp] theorem sylvesterEquiv_apply {S : Matrix n n ℝ} (hS : S.PosDef)
    (H : Matrix n n ℝ) : sylvesterEquiv hS H = S * H + H * S := rfl

theorem sylvester_contract : SylvesterContract n :=
  fun _ hS => ⟨sylvesterEquiv hS, sylvesterEquiv_apply hS⟩

theorem hasFDerivAt_sq (S : Matrix n n ℝ) :
    HasFDerivAt (fun A : Matrix n n ℝ => A * A) (sylvester S) S := by
  convert! (hasFDerivAt_id S).mul' (hasFDerivAt_id S) using 1

end ExactLiouvilleComparison.NormalizationSqrt
