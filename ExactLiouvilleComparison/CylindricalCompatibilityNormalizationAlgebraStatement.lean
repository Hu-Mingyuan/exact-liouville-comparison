import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Finite metric symplectic normalization: auxiliary contract

All matrices act on column vectors. The bilinear form represented by `W` is
`vᵀ W w`; consequently `g (A v) w = omega v w` means `A = -G⁻¹ W`.
The propositions below are targets, not proofs or construction assumptions.
-/
noncomputable section
open Matrix
open scoped MatrixOrder

namespace ExactLiouvilleComparison.NormalizationAlgebra

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Native bilinear form with the column-vector convention. -/
abbrev form {n : ℕ} (W : Mat n) := Matrix.toBilin' W

/-- Both input tensors transform by congruence under `v_old = P v_new`. -/
def pull {n : ℕ} (P W : Mat n) : Mat n := P.transpose * W * P

/-- The metric square root is the actual Mathlib real-matrix CFC square root. -/
def metricRoot {n : ℕ} (G : Mat n) : Mat n := CFC.sqrt G

/-- The Euclidean skew operator after whitening; the minus sign is essential. -/
def skew {n : ℕ} (G W : Mat n) : Mat n :=
  -(metricRoot G)⁻¹ * W * (metricRoot G)⁻¹

/-- Positive root of the negative square of the whitened skew operator. -/
def polarRoot {n : ℕ} (G W : Mat n) : Mat n :=
  CFC.sqrt (-(skew G W * skew G W))

/-- Explicit normalization formula, total on matrices; theorems impose admissibility. -/
def normalize {n : ℕ} (G W : Mat n) : Mat n :=
  (metricRoot G)⁻¹ * skew G W * (polarRoot G W)⁻¹ * metricRoot G

/-- Literal matrix version of compatibility, including strict positivity off zero. -/
def Compatible {n : ℕ} (W J : Mat n) : Prop :=
  J * J = -1 ∧ J.transpose * W * J = W ∧
    ∀ v : Vec n, v ≠ 0 → 0 < form W v (J *ᵥ v)

/-- No positive-rank or parity restriction is imposed on the input dimension. -/
def NormalizationContract : Prop :=
  ∀ (n : ℕ) (G W : Mat n), G.PosDef → W.transpose = -W → IsUnit W →
    Compatible W (normalize G W)

/-- Recovery of any compatible structure whose induced metric is the input metric. -/
def RecoveryContract : Prop :=
  ∀ (n : ℕ) (G W J₀ : Mat n), G.PosDef → W.transpose = -W → IsUnit W →
    Compatible W J₀ → G = W * J₀ → normalize G W = J₀

/-- Arbitrary invertible coordinate changes transform BOTH tensors. -/
def NaturalityContract : Prop :=
  ∀ (n : ℕ) (G W P : Mat n), G.PosDef → W.transpose = -W → IsUnit W →
    IsUnit P → normalize (pull P G) (pull P W) = P⁻¹ * normalize G W * P

end ExactLiouvilleComparison.NormalizationAlgebra
