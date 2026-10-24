import ExactLiouvilleComparison.Geometry
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Weak-taming linear algebra, with the compatible metric kept explicit. -/
noncomputable section
open scoped InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison

/-- The positive-parameter contraction estimate only needs nonnegative diagonal
of the bilinear form. No inverse or resolvent estimate is assumed. -/
theorem norm_le_of_weak_positive_equation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →ₗ[ℝ] Module.Dual ℝ E) (hB : ∀ v, 0 ≤ B v v)
    {t : ℝ} (ht : 0 < t) {X W : E}
    (heq : ∀ v, B X v + t * ⟪X, v⟫_ℝ = B W v) : ‖X‖ ≤ ‖W‖ := by
  have hpos := hB (X - W)
  have h := heq (X - W)
  simp only [map_sub, LinearMap.sub_apply] at hpos h
  have hi : ⟪X, X - W⟫_ℝ ≤ 0 := by nlinarith
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hi
  have hcs := real_inner_le_norm X W
  have hX := norm_nonneg X
  have hW := norm_nonneg W
  nlinarith

/-- Bilinear form version of the nondegeneracy assertion. In particular it
applies to alternating forms on every finite-dimensional real vector space.
The metric identity records exactly `h(v,w) = eta(v,Jw)`. -/
theorem weak_taming_linear_nondegenerate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega eta : E →ₗ[ℝ] Module.Dual ℝ E) (J : E →ₗ[ℝ] E)
    (hmetric : ∀ v w, ⟪v, w⟫_ℝ = eta v (J w))
    (hnd : ∀ v, (∀ w, omega v w = 0) → v = 0)
    (hweak : ∀ v, 0 ≤ omega v (J v)) {t : ℝ} (ht : 0 ≤ t) :
    ∀ v, (∀ w, (omega + t • eta) v w = 0) → v = 0 := by
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    simpa using hnd
  intro v hv
  have heq := hv (J v)
  change omega v (J v) + t * eta v (J v) = 0 at heq
  rw [← hmetric, real_inner_self_eq_norm_sq] at heq
  have h := hweak v
  have hsq : ‖v‖ ^ 2 ≤ 0 := by
    by_contra hsq
    have hp := mul_pos hpos (lt_of_not_ge hsq)
    linarith
  apply norm_eq_zero.mp
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

/-- Bilinear form version of the full contraction assertion, including `t = 0`.
Neither finite dimension nor alternation is needed beyond these hypotheses. -/
theorem weak_taming_linear_contraction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega eta : E →ₗ[ℝ] Module.Dual ℝ E) (J : E →ₗ[ℝ] E)
    (hmetric : ∀ v w, ⟪v, w⟫_ℝ = eta v (J w))
    (hnd : ∀ v, (∀ w, omega v w = 0) → v = 0)
    (hweak : ∀ v, 0 ≤ omega v (J v)) {t : ℝ} (ht : 0 ≤ t)
    (X W : E) (heq : ∀ v, (omega + t • eta) X v = omega W v) :
    ‖X‖ ≤ ‖W‖ := by
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    have hXW : X = W := by
      apply sub_eq_zero.mp
      apply hnd (X - W)
      intro v
      have h := heq v
      simp only [zero_smul, add_zero] at h
      simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using h
    exact le_of_eq (congrArg norm hXW)
  apply norm_le_of_weak_positive_equation ((LinearMap.dualMap J).comp omega)
    hweak hpos
  intro v
  rw [hmetric]
  exact heq (J v)

namespace CompatibleStructure
variable {d : ℕ} {M : SmoothManifold d} {reference : ExactSymplecticStructure M}

/-- The inner product uses exactly the core that defines the accepted metric norm. -/
instance metricInnerProductSpace (A : CompatibleStructure reference) (x : M.Point) :
    InnerProductSpace ℝ (A.MetricTangent x) :=
  InnerProductSpace.ofCore (A.metricCore x).toCore

/-- This is the actual compatible metric, not the chart inner product. -/
theorem metric_inner_eq (A : CompatibleStructure reference) (x : M.Point)
    (v w : A.MetricTangent x) :
    ⟪v, w⟫_ℝ = evalTwo (M.exteriorDerivative reference.primitive) x v (A.J x w) := by
  exact A.metric_eq x v w

/-- Lemma `lem:linear`, nondegeneracy, including the zero parameter. -/
theorem weak_taming_nondegenerate (A : CompatibleStructure reference)
    (omega : M.Form 2) (x : M.Point) (hnd : M.Nondegenerate omega x)
    (hweak : ∀ v, 0 ≤ evalTwo omega x v (A.J x v))
    {t : ℝ} (ht : 0 ≤ t) :
    M.Nondegenerate (omega + t • M.exteriorDerivative reference.primitive) x := by
  exact weak_taming_linear_nondegenerate (E := A.MetricTangent x)
    (A.flatLinear omega x) (A.flatLinear (M.exteriorDerivative reference.primitive) x)
    (A.J x).toLinearMap (A.metric_inner_eq x) hnd hweak ht

/-- Lemma `lem:linear`, contraction in the metric of the compatible summand. -/
theorem weak_taming_contraction (A : CompatibleStructure reference)
    (omega : M.Form 2) (x : M.Point) (hnd : M.Nondegenerate omega x)
    (hweak : ∀ v, 0 ≤ evalTwo omega x v (A.J x v))
    {t : ℝ} (ht : 0 ≤ t) (X W : A.MetricTangent x)
    (heq : ∀ v, evalTwo (omega + t • M.exteriorDerivative reference.primitive) x X v =
      evalTwo omega x W v) : ‖X‖ ≤ ‖W‖ := by
  exact weak_taming_linear_contraction (E := A.MetricTangent x)
    (A.flatLinear omega x) (A.flatLinear (M.exteriorDerivative reference.primitive) x)
    (A.J x).toLinearMap (A.metric_inner_eq x) hnd hweak ht X W heq

/-- Canonical pointwise inverse contractions satisfy the estimate. Their existence
is supplied by the accepted finite-dimensional `flatEquiv`, not by a flow assumption. -/
theorem inverseContraction_norm_le (A : CompatibleStructure reference)
    (omega : M.Form 2) (x : M.Point) (hnd : M.Nondegenerate omega x)
    (hweak : ∀ v, 0 ≤ evalTwo omega x v (A.J x v))
    {t : ℝ} (ht : 0 ≤ t) (l : A.Dual x) :
    ‖A.inverseContraction (omega + t • M.exteriorDerivative reference.primitive) x
      (A.weak_taming_nondegenerate omega x hnd hweak ht) l‖ ≤
    ‖A.inverseContraction omega x hnd l‖ := by
  apply A.weak_taming_contraction omega x hnd hweak ht
  intro v
  exact (A.inverseContraction_equation _ x _ l v).trans
    (A.inverseContraction_equation omega x hnd l v).symm

end CompatibleStructure
end ExactLiouvilleComparison
