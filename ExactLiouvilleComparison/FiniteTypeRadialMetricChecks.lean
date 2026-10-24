import ExactLiouvilleComparison.FiniteTypeRadialMetric

/-! Consumers in radius r and in the parent's c=1 radial-field notation. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.FiniteTypeRadialMetric

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (A : CompatibleStructure (completionReference C)) (cyl : CylindricalStructure C A)
    (R : C.ambient.manifold.Point → ℝ)
    (hR : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R) (hend : EndRadius C R)
include cyl hR hend

/-- Direct end consumer uses the manuscript radius inequality exp(t)>2. -/
theorem end_consumer (y : D.domain.boundary.Point) (t : ℝ) (ht : 2 < Real.exp t) :
    (∀ v, evalOne C.ambient.primitive (C.endMap (y, t)) v =
      -C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
        (A.J (C.endMap (y, t)) v)) ∧
    (A.dualNorm (C.endMap (y, t))
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) R (C.endMap (y, t)))) ^ 2 =
      Real.exp t := by
  have hlog := (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr ht
  exact ⟨primitive_identity C A cyl R hR hend y t hlog,
    (radius_dualNorm_sq C A cyl R hR hend y t hlog).trans (hend y t ht.le)⟩

/-- Literal c=1 identities supplied to the parent's radial reference construction. -/
theorem radial_fields_consumer (y : D.domain.boundary.Point) (t : ℝ)
    (ht : Real.log 2 < t) :
    (∀ v, evalOne (completionReference C).primitive (C.endMap (y, t)) v =
      -(1 : ℝ) * C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
        (A.J (C.endMap (y, t)) v)) ∧
    (1 : ℝ) * (A.dualNorm (C.endMap (y, t))
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) R (C.endMap (y, t)))) ^ 2 ≤
      R (C.endMap (y, t)) := by
  constructor
  · intro v
    simpa only [completionReference, neg_mul, one_mul] using primitive_identity C A cyl R hR hend y t ht v
  · rw [one_mul, radius_dualNorm_sq C A cyl R hR hend y t ht]

omit cyl hR hend in
theorem checked_target : Target := target

end ExactLiouvilleComparison.FiniteTypeRadialMetric
