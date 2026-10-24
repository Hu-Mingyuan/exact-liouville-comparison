import ExactLiouvilleComparison.ThirdPathStatement

/-! The literal third-path inverse field and its native endpoint regularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ThirdPath
variable {d : ℕ} {M : SmoothManifold d}

abbrev coefficient (P : RadialReference M) (T : ExactSymplecticStructure M) :=
  RadialInterpolationFlow.largeCoefficient P T.primitive T.smooth_primitive

theorem primitive_smooth (P : RadialReference M) (T : ExactSymplecticStructure M) (s : ℝ) :
    M.IsSmoothForm (primitive P T s) :=
  (coefficient P T).smooth_primitive.add (T.smooth_primitive.smul s)

theorem primitive_family (P : RadialReference M) (T : ExactSymplecticStructure M) :
    M.IsSmoothFormFamily (primitive P T) :=
  MoserRegularity.smoothFormFamily_affine _ _
    (coefficient P T).smooth_primitive T.smooth_primitive

/-- Affine differential used by the existing inverse regularity theorem. -/
def form (P : RadialReference M) (T : ExactSymplecticStructure M) (s : ℝ) : M.Form 2 :=
  M.exteriorDerivative (coefficient P T).primitive + s • M.exteriorDerivative T.primitive

theorem differential_eq (P : RadialReference M) (T : ExactSymplecticStructure M) (s : ℝ) :
    M.exteriorDerivative (primitive P T s) = form P T s := by
  change M.exteriorDerivative ((coefficient P T).primitive + s • T.primitive) = _
  rw [RadialInterpolation.exteriorDerivative_add (coefficient P T).smooth_primitive
    (T.smooth_primitive.smul s),
    M.exteriorDerivative_const_smul_one _ T.smooth_primitive]
  rfl

theorem form_apply (P : RadialReference M) (T : ExactSymplecticStructure M)
    (s : ℝ) (x : M.Point) (v w : M.Tangent x) :
    evalTwo (form P T s) x v w =
      evalTwo (M.exteriorDerivative (coefficient P T).primitive) x v w +
        s * evalTwo (M.exteriorDerivative T.primitive) x v w := rfl

theorem form_family (P : RadialReference M) (T : ExactSymplecticStructure M) :
    M.IsSmoothFormFamily (form P T) :=
  MoserRegularity.smoothFormFamily_affine _ _
    (M.isSmoothForm_exteriorDerivative _ (coefficient P T).smooth_primitive) T.symplectic.1

/-- The radial metric lower bound is in the explicit reference metric g. -/
theorem energy_lower (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) {s : ℝ} (hs : 0 ≤ s)
    (x : M.Point) (v : M.Tangent x) :
    LargeCoefficient.A P T.primitive (P.R x) *
      @norm (P.compatible.MetricTangent x) _ v ^ 2 ≤
        evalTwo (form P T s) x v (P.compatible.J x v) := by
  have hd : 0 ≤ (coefficient P T).rhoPrime (P.R x) := by
    rw [RadialInterpolationFlow.largeCoefficient_prime P T.primitive T.smooth_primitive
      (P.lower_R x)]
    exact LargeCoefficient.A_deriv_nonneg P T.primitive T.smooth_primitive _
  have h := (coefficient P T).metricValue_ge_of_nonneg x hd v
  have hn : @norm (P.compatible.MetricTangent x) _ v ^ 2 =
      P.compatible.g.inner x v v :=
    (@real_inner_self_eq_norm_sq (P.compatible.MetricTangent x) _ _ v).symm
  rw [hn, form_apply]
  exact h.trans (le_add_of_nonneg_right (mul_nonneg hs (hw x v)))

theorem nondegenerate (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) {s : ℝ} (hs : 0 ≤ s) (x : M.Point) :
    M.Nondegenerate (form P T s) x := by
  intro v hv
  have h := energy_lower P T hw hs x v
  rw [hv] at h
  have hA : 0 < LargeCoefficient.A P T.primitive (P.R x) :=
    lt_of_lt_of_le zero_lt_one (LargeCoefficient.one_le_A P T.primitive T.smooth_primitive _)
  have hn : @norm (P.compatible.MetricTangent x) _ v = 0 := by
    have hsq : @norm (P.compatible.MetricTangent x) _ v ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ hA).mp (by simpa only [mul_zero] using h)
    nlinarith [@norm_nonneg (P.compatible.MetricTangent x) _ v]
  exact norm_eq_zero.mp hn

theorem symplectic (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) :
    M.IsSymplecticOn (M.exteriorDerivative (primitive P T s.val)) univ := by
  apply (M.isSymplecticOn_exteriorDerivative_iff _ (primitive_smooth P T s.val) univ).2
  intro x _
  rw [differential_eq]
  exact nondegenerate P T hw s.property.1 x

/-- Actual positive inverse contraction of d mu_s applied to -lambda. -/
def field (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) : M.Tangent x :=
  P.compatible.inverseContraction (form P T s.val) x (nondegenerate P T hw s.property.1 x)
    (-P.compatible.covector x (LargeCoefficient.oneCovector T.primitive x))

theorem field_equation_form (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) (v : M.Tangent x) :
    evalTwo (form P T s.val) x (field P T hw s x) v = -evalOne T.primitive x v :=
  P.compatible.inverseContraction_equation _ x (nondegenerate P T hw s.property.1 x) _ v

theorem field_equation (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) (v : M.Tangent x) :
    evalTwo (M.exteriorDerivative (primitive P T s.val)) x (field P T hw s x) v =
      -evalOne T.primitive x v := by
  rw [differential_eq]
  exact field_equation_form P T hw s x v

theorem field_unique (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) (v : M.Tangent x)
    (hv : ∀ w, evalTwo (M.exteriorDerivative (primitive P T s.val)) x v w =
      -evalOne T.primitive x w) : v = field P T hw s x := by
  apply P.compatible.flatLinear_injective _ x (nondegenerate P T hw s.property.1 x)
  ext w
  rw [differential_eq] at hv
  exact (hv w).trans (field_equation_form P T hw s x w).symm

theorem field_joint (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) : MoserRegularity.NativeJoint (field P T hw) := by
  apply MoserRegularity.nativeJoint_of_equation (form P T) (fun _ => (-1 : ℝ) • T.primitive)
    (form_family P T) (MoserRegularity.smoothFormFamily_const _ (T.smooth_primitive.smul (-1)))
    (fun _ hs x => nondegenerate P T hw hs.1 x)
  intro s x w
  simpa only [show evalOne ((-1 : ℝ) • T.primitive) x w = -evalOne T.primitive x w by
    simp [evalOne]] using field_equation_form P T hw s x w

theorem field_intervalSmooth (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) : M.IsSmoothIntervalVectorFieldFamily (field P T hw) := by
  apply MoserRegularity.intervalSmooth_of_equation (form P T) (fun _ => (-1 : ℝ) • T.primitive)
    (form_family P T) (MoserRegularity.smoothFormFamily_const _ (T.smooth_primitive.smul (-1)))
    (fun _ hs x => nondegenerate P T hw hs.1 x)
  intro s x w
  simpa only [show evalOne ((-1 : ℝ) • T.primitive) x w = -evalOne T.primitive x w by
    simp [evalOne]] using field_equation_form P T hw s x w

end ExactLiouvilleComparison.ThirdPath
