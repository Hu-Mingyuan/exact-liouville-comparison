import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Native bundle contract for normalization from a supplied metric.
The propositions in this file are specifications, not existence proofs. -/

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ExactLiouvilleComparison.CylindricalCompatibility.Normalization

section Fiber
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Compatibility uses the positive convention `omega(v, J v) > 0`. -/
def Compatible (omega : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] V) : Prop :=
  (∀ v, J (J v) = -v) ∧
  (∀ v w, omega (J v) (J w) = omega v w) ∧
  (∀ v, v ≠ 0 → 0 < omega v (J v))

end Fiber

section Bundle
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB)
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- A smooth fiberwise alternating nondegenerate form on the native bundle.
No closedness condition is meaningful or needed for a general vector bundle. -/
structure SymplecticForm where
  form : (x : B) → E x →L[ℝ] E x →L[ℝ] ℝ
  smooth : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (form x))
  alternating : ∀ x v, form x v v = 0
  nondegenerate : ∀ x v, (∀ w, form x v w = 0) → v = 0

/-- Normalization from a supplied native smooth positive definite metric.
Recovery is fiberwise and requires no global prescribed complex structure. -/
def NormalizationTarget [IsManifold IB ∞ B] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F E IB] (omega : SymplecticForm IB F E)
    (h : ContMDiffRiemannianMetric IB ∞ F E) : Prop :=
  ∃ J : (x : B) → E x →L[ℝ] E x,
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) x (J x)) ∧
    (∀ x, Compatible (omega.form x) (J x)) ∧
    (∀ x (J₀ : E x →L[ℝ] E x), Compatible (omega.form x) J₀ →
      (∀ v w, h.inner x v w = omega.form x v (J₀ w)) → J x = J₀)

end Bundle
end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
