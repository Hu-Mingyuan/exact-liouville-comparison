import ExactLiouvilleComparison.LinearAlgebra
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Pointwise radial linear algebra in the explicit compatible metric. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison

/-- Two orthogonal vectors of equal length give the unnormalized two-plane
Bessel inequality, including when both vectors vanish. -/
theorem two_plane_inner_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u w v : E) (huw : ⟪u, w⟫_ℝ = 0) (hn : ⟪w, w⟫_ℝ = ⟪u, u⟫_ℝ) :
    ⟪u, v⟫_ℝ ^ 2 + ⟪w, v⟫_ℝ ^ 2 ≤ ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ := by
  have hwu : ⟪w, u⟫_ℝ = 0 := by rw [real_inner_comm, huw]
  have h := real_inner_mul_inner_self_le
    (⟪u, v⟫_ℝ • u + ⟪w, v⟫_ℝ • w) v
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, huw, hwu, hn, mul_zero, add_zero, zero_add] at h
  have hn0 : 0 ≤ ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ :=
    mul_nonneg real_inner_self_nonneg real_inner_self_nonneg
  nlinarith [sq_nonneg ⟪u, v⟫_ℝ, sq_nonneg ⟪w, v⟫_ℝ]

namespace CompatibleStructure
variable {d : ℕ} {M : SmoothManifold d} {S : ExactSymplecticStructure M}
variable (A : CompatibleStructure S)

theorem inner_J_J (x : M.Point) (v w : A.MetricTangent x) :
    @inner ℝ (A.MetricTangent x) _ (A.J x v) (A.J x w) = ⟪v, w⟫_ℝ := by
  change A.g.inner x (A.J x v) (A.J x w) = A.g.inner x v w
  rw [A.metric_eq, A.metric_eq, A.invariant]

/-- `J` is orthogonal in `g`, not in an arbitrary chart norm. -/
def metricJ (x : M.Point) : A.MetricTangent x →ₗᵢ[ℝ] A.MetricTangent x :=
  (show A.MetricTangent x →ₗ[ℝ] A.MetricTangent x from (A.J x).toLinearMap).isometryOfInner
    (A.inner_J_J x)

theorem inner_J_left (x : M.Point) (v w : A.MetricTangent x) :
    ⟪A.metricJ x v, w⟫_ℝ = -⟪v, A.metricJ x w⟫_ℝ := by
  have h := A.inner_J_J x v (A.J x w)
  rw [A.square] at h
  change ⟪A.metricJ x v, -w⟫_ℝ = ⟪v, A.metricJ x w⟫_ℝ at h
  rw [inner_neg_right] at h
  linarith

theorem inner_J_self (x : M.Point) (v : A.MetricTangent x) :
    ⟪v, A.metricJ x v⟫_ℝ = 0 := by
  have h := A.inner_J_left x v v
  rw [real_inner_comm] at h
  linarith

/-- The two covectors `l` and `l composed J` satisfy the sharp two-plane bound. -/
theorem covector_two_plane_le (x : M.Point) (l : A.Dual x) (v : A.MetricTangent x) :
    l v ^ 2 + l (A.J x v) ^ 2 ≤ ‖l‖ ^ 2 * ‖v‖ ^ 2 := by
  let z := (InnerProductSpace.toDual ℝ (A.MetricTangent x)).symm l
  have hz (w : A.MetricTangent x) : ⟪z, w⟫_ℝ = l w :=
    InnerProductSpace.toDual_symm_apply
  have hn : ‖z‖ = ‖l‖ := (InnerProductSpace.toDual ℝ (A.MetricTangent x)).symm.norm_map l
  have h := two_plane_inner_sq_le z (A.metricJ x z) v (A.inner_J_self x z)
    (A.inner_J_J x z z)
  rw [A.inner_J_left, hz, hz, neg_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, hn] at h
  exact h

end CompatibleStructure
end ExactLiouvilleComparison
