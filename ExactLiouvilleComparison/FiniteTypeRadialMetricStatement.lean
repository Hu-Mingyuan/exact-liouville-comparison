import ExactLiouvilleComparison.Statement

/-! Bounded cylindrical end calculation; the target below is a specification. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison.FiniteTypeRadialMetric

/-- Literal end equality only; no derivative or metric information is assumed. -/
def EndRadius {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (R : C.ambient.manifold.Point → ℝ) : Prop :=
  ∀ y t, 2 ≤ Real.exp t → R (C.endMap (y, t)) = Real.exp t

/-- The local calculation in the proof of manuscript `cor:liouville`.
The smooth function is supplied by the radius-construction owner. -/
def Target : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D)
    (A : CompatibleStructure (completionReference C)), CylindricalStructure C A →
    ∀ R : C.ambient.manifold.Point → ℝ,
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R → EndRadius C R →
    ∀ y t, Real.log 2 < t →
      (∀ v, evalOne C.ambient.primitive (C.endMap (y, t)) v =
        -C.ambient.manifold.scalarDerivative R (C.endMap (y, t))
          (A.J (C.endMap (y, t)) v)) ∧
      (A.dualNorm (C.endMap (y, t))
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) R (C.endMap (y, t)))) ^ 2 =
        R (C.endMap (y, t))

end ExactLiouvilleComparison.FiniteTypeRadialMetric
