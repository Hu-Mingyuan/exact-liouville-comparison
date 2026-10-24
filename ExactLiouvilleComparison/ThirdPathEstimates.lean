import ExactLiouvilleComparison.ThirdPathField

/-! Explicit reference-g estimates for the constructed third-path field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ThirdPath
variable {d : ℕ} {M : SmoothManifold d}

theorem field_norm_bound (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) :
    @norm (P.compatible.MetricTangent x) _ (field P T hw s x) ≤
      P.compatible.dualNorm x (LargeCoefficient.oneCovector T.primitive x) /
        LargeCoefficient.A P T.primitive (P.R x) := by
  let v : P.compatible.MetricTangent x := field P T hw s x
  let L := P.compatible.covector x (LargeCoefficient.oneCovector T.primitive x)
  let a := LargeCoefficient.A P T.primitive (P.R x)
  have ha : 0 < a :=
    lt_of_lt_of_le zero_lt_one (LargeCoefficient.one_le_A P T.primitive T.smooth_primitive _)
  have henergy : a * ‖v‖ ^ 2 ≤ -evalOne T.primitive x (P.compatible.J x v) := by
    have h := energy_lower P T hw s.property.1 x v
    rw [field_equation_form] at h
    exact h
  have hdual : |evalOne T.primitive x (P.compatible.J x v)| ≤ ‖L‖ * ‖v‖ := by
    have h := L.le_opNorm (P.compatible.metricJ x v)
    rw [(P.compatible.metricJ x).norm_map] at h
    exact h
  have h : a * ‖v‖ ^ 2 ≤ ‖L‖ * ‖v‖ :=
    henergy.trans ((neg_le_abs _).trans hdual)
  change ‖v‖ ≤ ‖L‖ / a
  by_cases hv : ‖v‖ = 0
  · rw [hv]
    exact div_nonneg (norm_nonneg _) ha.le
  · have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    apply (le_div_iff₀ ha).2
    apply (mul_le_mul_iff_of_pos_right hpos).mp
    calc
      (‖v‖ * a) * ‖v‖ = a * ‖v‖ ^ 2 := by ring
      _ ≤ ‖L‖ * ‖v‖ := h

theorem ratio_le_one (P : RadialReference M) (T : ExactSymplecticStructure M) (x : M.Point) :
    P.compatible.dualNorm x (LargeCoefficient.oneCovector T.primitive x) /
      LargeCoefficient.A P T.primitive (P.R x) ≤ 1 := by
  have ha : 0 < LargeCoefficient.A P T.primitive (P.R x) :=
    lt_of_lt_of_le zero_lt_one (LargeCoefficient.one_le_A P T.primitive T.smooth_primitive _)
  apply (div_le_one ha).2
  have h := LargeCoefficient.A_dominates P T.primitive T.smooth_primitive x
  linarith

theorem field_norm_le_one (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) :
    @norm (P.compatible.MetricTangent x) _ (field P T hw s x) ≤ 1 :=
  (field_norm_bound P T hw s x).trans (ratio_le_one P T x)

end ExactLiouvilleComparison.ThirdPath
