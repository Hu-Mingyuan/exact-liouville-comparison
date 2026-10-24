import ExactLiouvilleComparison.FiniteTypeRadialMetricStatement
import ExactLiouvilleComparison.LinearAlgebra
import FsFltz.Geometry.BoundarySmooth
import FsFltz.Geometry.FlowBridge
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison.FiniteTypeRadialMetric

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- Every native tangent vector has end coordinates, in every dimension. -/
theorem end_derivative_surjective (y : D.domain.boundary.Point) (t : ℝ) :
    Function.Surjective (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) C.endMap (y, t)) :=
  ((C.endMap_isLocalDiffeomorph (y, t)).mfderivToContinuousLinearEquiv
    (by simp)).surjective

/-- Differentiate the literal end equality on an open neighborhood. -/
theorem radius_end_derivative (R : C.ambient.manifold.Point → ℝ)
    (hR : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R) (hend : EndRadius C R)
    (y : D.domain.boundary.Point) (t : ℝ) (ht : Real.log 2 < t)
    (v : D.domain.boundary.Tangent y) (s : ℝ) :
    C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (v, s)) = Real.exp t * s := by
  have hexp : 2 < Real.exp t := (Real.log_lt_iff_lt_exp (by norm_num)).mp ht
  have heq : (R ∘ C.endMap) =ᶠ[𝓝 (y, t)]
      (fun p : D.domain.boundary.Point × ℝ => Real.exp p.2) := by
    filter_upwards [(Real.continuous_exp.comp continuous_snd).continuousAt.eventually
      (Ioi_mem_nhds hexp)] with p hp
    exact hend p.1 p.2 (le_of_lt hp)
  have hd := (Real.hasDerivAt_exp t).hasFDerivAt.hasMFDerivAt.comp (y, t)
    (hasMFDerivAt_snd (I := 𝓘(ℝ, Model (d - 1))) (I' := 𝓘(ℝ, ℝ)) (y, t))
  have hc := mfderiv_comp (y, t) (hR.mdifferentiableAt (by simp))
    (C.smooth_endMap.mdifferentiableAt (by simp))
  have he := heq.mfderiv_eq (I := ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))))
    (I' := 𝓘(ℝ, ℝ))
  change mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ))
      (R ∘ C.endMap) (y, t) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ))
      (Real.exp ∘ Prod.snd) (y, t) at he
  rw [hc, hd.mfderiv] at he
  have hv := congrArg (fun f => f (v, s)) he
  change C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (v, s)) = s * Real.exp t at hv
  exact hv.trans (mul_comm _ _)

/-- The end's time tangent is the original complete Liouville field. -/
theorem end_time_derivative (y : D.domain.boundary.Point) (t : ℝ) :
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
      C.endMap (y, t) (0, 1) = C.ambient.field (C.endMap (y, t)) := by
  have hp := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, Model (d - 1))) y t).prodMk (hasMFDerivAt_id t)
  have hc := (C.smooth_endMap.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hp
  have hf := C.ambient.completeFlow.isMIntegralCurve
    (C.inclusion.map (D.domain.boundaryInclusion.map y)) t
  have heq : (C.endMap ∘ fun s : ℝ => (y, s)) =
      (fun s => C.ambient.completeFlow.flow s
        (C.inclusion.map (D.domain.boundaryInclusion.map y))) := by
    funext s
    exact C.end_flow y s
  have hd := hc.mfderiv
  dsimp only [id_eq] at hd
  rw [heq, hf.mfderiv] at hd
  have h := congrArg (fun f => f (1 : ℝ)) hd
  change (1 : ℝ) • C.ambient.field
      (C.ambient.completeFlow.flow t
        (C.inclusion.map (D.domain.boundaryInclusion.map y))) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
      C.endMap (y, t) (0, 1) at h
  have hpnt : C.ambient.completeFlow.flow.toFun t
      (C.inclusion.map (D.domain.boundaryInclusion.map y)) = C.endMap (y, t) :=
    (C.end_flow y t).symm
  rw [hpnt, one_smul] at h
  exact h.symm

variable (A : CompatibleStructure (completionReference C)) (cyl : CylindricalStructure C A)
include cyl

/-- The equality holds on every ambient tangent vector, not only end test vectors. -/
theorem primitive_identity (R : C.ambient.manifold.Point → ℝ)
    (hR : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R) (hend : EndRadius C R)
    (y : D.domain.boundary.Point) (t : ℝ) (ht : Real.log 2 < t)
    (w : C.ambient.manifold.Tangent (C.endMap (y, t))) :
    evalOne C.ambient.primitive (C.endMap (y, t)) w =
      -C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
        (A.J (C.endMap (y, t)) w) := by
  obtain ⟨⟨v, s⟩, rfl⟩ := end_derivative_surjective C y t w
  have ht0 : 0 ≤ t := le_of_lt ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans ht)
  rw [cyl.cylindrical y t ht0, radius_end_derivative C R hR hend y t ht,
    C.end_primitive]
  ring

/-- Positive contraction and the primitive identity identify the actual g-gradient. -/
theorem field_inner (R : C.ambient.manifold.Point → ℝ)
    (hR : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R) (hend : EndRadius C R)
    (y : D.domain.boundary.Point) (t : ℝ) (ht : Real.log 2 < t)
    (w : A.MetricTangent (C.endMap (y, t))) :
    inner ℝ (show A.MetricTangent (C.endMap (y, t)) from
      C.ambient.field (C.endMap (y, t))) w =
      C.ambient.manifold.scalarDerivative R (C.endMap (y, t)) w := by
  rw [A.metric_inner_eq]
  change evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
    (C.endMap (y, t)) (C.ambient.field (C.endMap (y, t)))
      (A.J (C.endMap (y, t)) w) = _
  rw [C.ambient.contraction, primitive_identity C A cyl R hR hend y t ht, A.square]
  simp only [scalarDerivative, map_neg, neg_neg]

/-- Exact g-dual square, obtained from the native Riesz isometry. -/
theorem radius_dualNorm_sq (R : C.ambient.manifold.Point → ℝ)
    (hR : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R) (hend : EndRadius C R)
    (y : D.domain.boundary.Point) (t : ℝ) (ht : Real.log 2 < t) :
    (A.dualNorm (C.endMap (y, t))
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) R (C.endMap (y, t)))) ^ 2 =
      R (C.endMap (y, t)) := by
  let z : A.MetricTangent (C.endMap (y, t)) := C.ambient.field (C.endMap (y, t))
  let l := A.covector (C.endMap (y, t))
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) R (C.endMap (y, t)))
  have hre : l = (InnerProductSpace.toDual ℝ (A.MetricTangent (C.endMap (y, t)))) z := by
    ext w
    exact (field_inner C A cyl R hR hend y t ht w).symm
  change ‖l‖ ^ 2 = _
  calc
    ‖l‖ ^ 2 = ‖z‖ ^ 2 := by rw [hre, (InnerProductSpace.toDual ℝ _).norm_map]
    _ = inner ℝ z z := (real_inner_self_eq_norm_sq z).symm
    _ = C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
        (C.ambient.field (C.endMap (y, t))) := field_inner C A cyl R hR hend y t ht z
    _ = Real.exp t := by
      rw [← end_time_derivative C y t, radius_end_derivative C R hR hend y t ht]
      exact mul_one _
    _ = R (C.endMap (y, t)) :=
      (hend y t (le_of_lt ((Real.log_lt_iff_lt_exp (by norm_num)).mp ht))).symm

omit cyl in
/-- Actual proof of the independently reviewed bounded specification. -/
theorem target : Target := by
  intro d D C A cyl R hR hend y t ht
  exact ⟨primitive_identity C A cyl R hR hend y t ht,
    radius_dualNorm_sq C A cyl R hR hend y t ht⟩

end ExactLiouvilleComparison.FiniteTypeRadialMetric
