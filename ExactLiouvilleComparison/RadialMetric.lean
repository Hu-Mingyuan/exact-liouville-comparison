import ExactLiouvilleComparison.RadialCoefficient
import ExactLiouvilleComparison.RadialMetricLinear
import FsFltz.Geometry.FormScalarDerivative
import FsFltz.Geometry.SmoothForms

/-! Native radial exterior derivative and metric formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison
namespace RadialCoefficient
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}
variable (q : RadialCoefficient P.rstar)

abbrev primitive : M.Form 1 := LinearAlgebraChecks.radialPrimitive P q.rho

theorem smooth_primitive : M.IsSmoothForm q.primitive :=
  P.exactStructure.smooth_primitive.function_smul q.smooth_comp

/-- Product and chain rules for the native exterior derivative. -/
theorem exteriorDerivative_apply (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative q.primitive) x v w =
      q.rho (P.R x) * evalTwo (M.exteriorDerivative P.exactStructure.primitive) x v w +
      q.rhoPrime (P.R x) * (M.scalarDerivative P.R x v *
        evalOne P.exactStructure.primitive x w -
        M.scalarDerivative P.R x w * evalOne P.exactStructure.primitive x v) := by
  change evalTwo (M.exteriorDerivative (fun y => (q.rho ∘ P.R) y •
    P.exactStructure.primitive y)) x v w = _
  rw [M.evalTwo_exteriorDerivative_smul (q.rho ∘ P.R) _ q.smooth_comp
    P.exactStructure.smooth_primitive]
  rw [q.scalarDerivative_comp, q.scalarDerivative_comp]
  simp only [Function.comp_apply]
  ring

/-- The actual bilinear expression `d(rho(R) beta)(v,Jw)`. -/
def metricValue (x : M.Point) (v w : M.Tangent x) : ℝ :=
  evalTwo (M.exteriorDerivative q.primitive) x v (P.compatible.J x w)

/-- No radial identity is used on the compact core, including its boundary. -/
theorem metricValue_core (x : M.Point) (hx : P.R x ≤ P.rstar) (v w : M.Tangent x) :
    q.metricValue x v w = q.rho (P.R x) * P.compatible.g.inner x v w := by
  unfold metricValue
  rw [q.exteriorDerivative_apply, q.rhoPrime_eq_zero ⟨P.lower_R x, hx⟩,
    zero_mul, add_zero, ← P.compatible.metric_eq]

/-- The radial formula outside the core, with the positive contraction sign. -/
theorem metricValue_exterior (x : M.Point) (hx : P.rstar < P.R x)
    (v w : M.Tangent x) :
    q.metricValue x v w = q.rho (P.R x) * P.compatible.g.inner x v w +
      P.c * q.rhoPrime (P.R x) *
        (M.scalarDerivative P.R x v * M.scalarDerivative P.R x w +
          M.scalarDerivative P.R x (P.compatible.J x v) *
            M.scalarDerivative P.R x (P.compatible.J x w)) := by
  unfold metricValue
  rw [q.exteriorDerivative_apply, ← P.compatible.metric_eq,
    P.radial_identity x hx, P.radial_identity x hx, P.compatible.square]
  simp only [scalarDerivative, map_neg]
  ring

/-- The same formula holds globally because the derivative vanishes on the core. -/
theorem metricValue_eq (x : M.Point) (v w : M.Tangent x) :
    q.metricValue x v w = q.rho (P.R x) * P.compatible.g.inner x v w +
      P.c * q.rhoPrime (P.R x) *
        (M.scalarDerivative P.R x v * M.scalarDerivative P.R x w +
          M.scalarDerivative P.R x (P.compatible.J x v) *
            M.scalarDerivative P.R x (P.compatible.J x w)) := by
  by_cases hx : P.R x ≤ P.rstar
  · rw [q.metricValue_core x hx, q.rhoPrime_eq_zero ⟨P.lower_R x, hx⟩]
    ring
  · exact q.metricValue_exterior x (lt_of_not_ge hx) v w

theorem metricValue_symm (x : M.Point) (v w : M.Tangent x) :
    q.metricValue x v w = q.metricValue x w v := by
  rw [q.metricValue_eq, q.metricValue_eq, P.compatible.g.symm x w v]
  ring

/-- The manuscript scalar `a`, using exactly the reference dual norm. -/
def radialA (_q : RadialCoefficient P.rstar) (x : M.Point) : ℝ :=
  P.c * (P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)) ^ 2

/-- The radial eigenvalue, with no division by `dR`. -/
def radialD (x : M.Point) : ℝ := q.rho (P.R x) + q.rhoPrime (P.R x) * q.radialA x

theorem radialA_nonneg (x : M.Point) : 0 ≤ q.radialA x :=
  mul_nonneg P.positive_c.le (sq_nonneg _)

theorem radialD_pos (x : M.Point) (hx : P.rstar < P.R x) : 0 < q.radialD x := by
  have ha := P.radial_bound x hx
  change q.radialA x ≤ P.R x at ha
  have hp := q.positive (P.R x) (P.lower_R x)
  have hm := q.radial_positive (P.R x) (P.lower_R x)
  change 0 < q.rho (P.R x) + P.R x * q.rhoPrime (P.R x) at hm
  unfold radialD
  by_cases hd : 0 ≤ q.rhoPrime (P.R x)
  · exact add_pos_of_pos_of_nonneg hp (mul_nonneg hd (q.radialA_nonneg x))
  · have h := mul_le_mul_of_nonpos_left ha (le_of_not_ge hd)
    linarith

/-- The radial perturbation is bounded by `a g`, before the end bound `a ≤ R`. -/
theorem radial_tensor_le (x : M.Point) (v : M.Tangent x) :
    P.c * ((M.scalarDerivative P.R x v)^2 +
      (M.scalarDerivative P.R x (P.compatible.J x v))^2) ≤
      q.radialA x * P.compatible.g.inner x v v := by
  have h := P.compatible.covector_two_plane_le x
    (P.compatible.covector x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)) v
  have hn : (@norm (P.compatible.MetricTangent x) _ v) ^ 2 =
      P.compatible.g.inner x v v := (@real_inner_self_eq_norm_sq (P.compatible.MetricTangent x) _ _ v).symm
  rw [hn] at h
  have hc := mul_le_mul_of_nonneg_left h P.positive_c.le
  change P.c * ((M.scalarDerivative P.R x v)^2 +
    (M.scalarDerivative P.R x (P.compatible.J x v))^2) ≤
    P.c * ((P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x))^2 *
      P.compatible.g.inner x v v) at hc
  unfold radialA
  nlinarith only [hc]

theorem metricValue_le_of_nonpos (x : M.Point) (hd : q.rhoPrime (P.R x) ≤ 0)
    (v : M.Tangent x) :
    q.metricValue x v v ≤ q.rho (P.R x) * P.compatible.g.inner x v v := by
  rw [q.metricValue_eq]
  have h := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos P.positive_c.le hd)
    (add_nonneg (sq_nonneg (M.scalarDerivative P.R x v))
      (sq_nonneg (M.scalarDerivative P.R x (P.compatible.J x v))))
  nlinarith

theorem metricValue_ge_of_nonneg (x : M.Point) (hd : 0 ≤ q.rhoPrime (P.R x))
    (v : M.Tangent x) :
    q.rho (P.R x) * P.compatible.g.inner x v v ≤ q.metricValue x v v := by
  rw [q.metricValue_eq]
  have h := mul_nonneg (mul_nonneg P.positive_c.le hd)
    (add_nonneg (sq_nonneg (M.scalarDerivative P.R x v))
      (sq_nonneg (M.scalarDerivative P.R x (P.compatible.J x v))))
  nlinarith

theorem metricValue_lower_of_nonpos (x : M.Point) (hd : q.rhoPrime (P.R x) ≤ 0)
    (v : M.Tangent x) :
    (q.rho (P.R x) + P.R x * q.rhoPrime (P.R x)) * P.compatible.g.inner x v v ≤
      q.metricValue x v v := by
  by_cases hx : P.R x ≤ P.rstar
  · rw [q.rhoPrime_eq_zero ⟨P.lower_R x, hx⟩, q.metricValue_core x hx]
    simp
  have hg : 0 ≤ P.compatible.g.inner x v v := by
    by_cases hv : v = 0
    · subst v; simp
    · exact (P.compatible.g.pos x v hv).le
  have ht := q.radial_tensor_le x v
  have ha := mul_le_mul_of_nonneg_right (P.radial_bound x (lt_of_not_ge hx)) hg
  change q.radialA x * P.compatible.g.inner x v v ≤ _ at ha
  have hb := mul_le_mul_of_nonpos_left (ht.trans ha) hd
  rw [q.metricValue_eq]
  nlinarith

/-- Positivity is derived from the two-plane bound and coefficient hypotheses. -/
theorem metricValue_pos (x : M.Point) (v : M.Tangent x) (hv : v ≠ 0) :
    0 < q.metricValue x v v := by
  have hg := P.compatible.g.pos x v hv
  by_cases hd : 0 ≤ q.rhoPrime (P.R x)
  · exact lt_of_lt_of_le (mul_pos (q.positive (P.R x) (P.lower_R x)) hg)
      (q.metricValue_ge_of_nonneg x hd v)
  · exact lt_of_lt_of_le (mul_pos (q.radial_positive (P.R x) (P.lower_R x)) hg)
      (q.metricValue_lower_of_nonpos x (le_of_not_ge hd) v)

/-- The exact symplectic structure is constructed, with actual native exterior
 derivative, smoothness and closedness; nondegeneracy follows from positivity. -/
def exactStructure : ExactSymplecticStructure M where
  primitive := q.primitive
  smooth_primitive := q.smooth_primitive
  symplectic := (M.isSymplecticOn_exteriorDerivative_iff _ q.smooth_primitive univ).2 (by
    intro x _ v hv
    by_contra h
    have hp := q.metricValue_pos x v h
    have hz := hv (P.compatible.J x v)
    change q.metricValue x v v = 0 at hz
    linarith)

end RadialCoefficient
end ExactLiouvilleComparison
