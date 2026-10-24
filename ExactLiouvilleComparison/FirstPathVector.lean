import ExactLiouvilleComparison.FirstPathCoefficient

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPath
variable {d : ℕ} {M : SmoothManifold d}
open SmallCoefficient LinearAlgebraChecks

def form (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (t : ℝ) : M.Form 2 :=
  M.exteriorDerivative T.primitive +
    t • M.exteriorDerivative (radialPrimitive P (k G P.rstar))

theorem nondegenerate (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) {t : ℝ} (ht : 0 ≤ t) : M.Nondegenerate (form P G T t) x :=
  (RadialMetricChecks.first_path_linear_estimate P (coefficient P G) T hw x ht).1

def W (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (x : M.Point) : P.compatible.MetricTangent x :=
  P.compatible.inverseContraction (M.exteriorDerivative T.primitive) x
    (T.symplectic.2.2 x (mem_univ x)) (firstPathCovector P (k G P.rstar) P.compatible x)

def X (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) : P.compatible.MetricTangent x :=
  P.compatible.inverseContraction (form P G T t) x (nondegenerate P G T hw x ht)
    (firstPathCovector P (k G P.rstar) P.compatible x)

theorem W_equation (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (x : M.Point) (v : M.Tangent x) :
    evalTwo (M.exteriorDerivative T.primitive) x (W P G T x) v =
      -k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x v :=
  P.compatible.inverseContraction_equation _ x _ _ v

theorem X_equation (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) (v : M.Tangent x) :
    evalTwo (form P G T t) x (X P G T hw x t ht) v =
      -k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x v :=
  P.compatible.inverseContraction_equation _ x _ _ v

theorem solution_unique (P : RadialReference M) (eta : M.Form 2) (x : M.Point)
    (hn : M.Nondegenerate eta x) (u v : M.Tangent x)
    (he : ∀ w, evalTwo eta x u w = evalTwo eta x v w) : u = v := by
  apply P.compatible.flatLinear_injective eta x hn
  ext w
  exact he w

theorem X_unique (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) (v : M.Tangent x)
    (he : ∀ w, evalTwo (form P G T t) x v w =
      -k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w) :
    v = X P G T hw x t ht :=
  solution_unique P _ x (nondegenerate P G T hw x ht) _ _
    (fun w => (he w).trans (X_equation P G T hw x t ht w).symm)

theorem W_unique (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (x : M.Point) (v : M.Tangent x)
    (he : ∀ w, evalTwo (M.exteriorDerivative T.primitive) x v w =
      -k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w) :
    v = W P G T x :=
  solution_unique P _ x (T.symplectic.2.2 x (mem_univ x)) _ _
    (fun w => (he w).trans (W_equation P G T x w).symm)

theorem X_zero (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) (x : M.Point) :
    X P G T hw x 0 le_rfl = W P G T x := by
  apply W_unique
  intro w
  simpa [form] using X_equation P G T hw x 0 le_rfl w

theorem covector_norm (P : RadialReference M) (G : AdmissibleGrowth 1) (x : M.Point) :
    ‖firstPathCovector P (k G P.rstar) P.compatible x‖ =
      k G P.rstar (P.R x) * P.compatible.dualNorm x (P.betaCovector x) := by
  have he : firstPathCovector P (k G P.rstar) P.compatible x =
      -k G P.rstar (P.R x) • P.compatible.covector x (P.betaCovector x) := by
    ext v
    rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (k_pos G _ _)]
  rfl

theorem W_bound (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (x : M.Point) {C : ℝ}
    (hb : P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ‖W P G T x‖ ≤ C * G.B (P.R x) * k G P.rstar (P.R x) *
      P.compatible.dualNorm x (P.betaCovector x) := by
  have h := (P.compatible.inverseContraction (M.exteriorDerivative T.primitive) x
    (T.symplectic.2.2 x (mem_univ x))).le_opNorm
      (firstPathCovector P (k G P.rstar) P.compatible x)
  change ‖W P G T x‖ ≤ P.compatible.inverseNorm T x * _ at h
  apply h.trans
  calc
    _ ≤ (C * G.B (P.R x)) * ‖firstPathCovector P (k G P.rstar) P.compatible x‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by rw [covector_norm]; ring

/-- The metric argument fixes the norm instance before the native vector is supplied. -/
def tangentNorm {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (x : M.Point) (v : M.Tangent x) : ℝ :=
  @norm (A.MetricTangent x) inferInstance v

theorem X_h_bound (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) :
    tangentNorm (coefficient P G).compatible x (X P G T hw x t ht) ≤
      tangentNorm (coefficient P G).compatible x (W P G T x) := by
  apply (coefficient P G).compatible.weak_taming_contraction
    (M.exteriorDerivative T.primitive) x (T.symplectic.2.2 x (mem_univ x))
    (hw x) ht
  intro v
  exact (X_equation P G T hw x t ht v).trans (W_equation P G T x v).symm

theorem norm_sq_metric {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (x : M.Point) (v : A.MetricTangent x) : ‖v‖ ^ 2 = A.g.inner x v v :=
  (real_inner_self_eq_norm_sq v).symm

theorem X_g_bound (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) :
    ‖X P G T hw x t ht‖ ≤ Real.sqrt (k G P.rstar (P.R x) / m G P.rstar (P.R x)) *
      ‖W P G T x‖ := by
  have hX := (metric_bounds P G x (X P G T hw x t ht)).1
  have hW := (metric_bounds P G x (W P G T x)).2
  have hh := X_h_bound P G T hw x t ht
  have hs := sq_le_sq₀
    (@norm_nonneg ((coefficient P G).compatible.MetricTangent x) _ (X P G T hw x t ht))
    (@norm_nonneg ((coefficient P G).compatible.MetricTangent x) _ (W P G T x))
  rw [← norm_sq_metric, ← norm_sq_metric] at hX hW
  have hsq := hs.mpr hh
  have hm := m_pos G P.rstar (P.lower_R x)
  have hk := k_pos G P.rstar (P.R x)
  have he := Real.sq_sqrt (div_nonneg hk.le hm.le)
  have hmain : m G P.rstar (P.R x) * ‖X P G T hw x t ht‖ ^ 2 ≤
      k G P.rstar (P.R x) * ‖W P G T x‖ ^ 2 := hX.trans (hsq.trans hW)
  have hdiv : ‖X P G T hw x t ht‖ ^ 2 ≤
      k G P.rstar (P.R x) / m G P.rstar (P.R x) * ‖W P G T x‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).mpr
    nlinarith [hmain]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, he]
  exact hdiv

end ExactLiouvilleComparison.FirstPath
