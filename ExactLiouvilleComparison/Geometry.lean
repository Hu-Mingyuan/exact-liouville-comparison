import FsFltz.Geometry.FixedAmbient
import FsFltz.Geometry.ExteriorDerivative
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! Native geometric definitions for the statement gate. No comparison theorem is asserted. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison

structure ExactSymplecticStructure {d : ℕ} (M : SmoothManifold d) where
  primitive : M.Form 1
  smooth_primitive : M.IsSmoothForm primitive
  symplectic : M.IsSymplecticOn (M.exteriorDerivative primitive) univ

/-- Native smoothness of a section of the tangent endomorphism bundle. -/
def SmoothEndomorphism {d : ℕ} (M : SmoothManifold d)
    (J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x) : Prop :=
  ContMDiff (𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).prod
    (𝓘(ℝ, Model d →L[ℝ] Model d))) ∞
    (fun x => Bundle.TotalSpace.mk' (Model d →L[ℝ] Model d) x (J x))

/-- The supplied inner product is required to be exactly dβ(.,J.).
It uses the native smooth Riemannian metric, not estimates or existence conclusions. -/
structure CompatibleStructure {d : ℕ} {M : SmoothManifold d}
    (reference : ExactSymplecticStructure M) where
  J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x
  smooth_J : SmoothEndomorphism M J
  square : ∀ x v, J x (J x v) = -v
  invariant : ∀ x v w,
    evalTwo (M.exteriorDerivative reference.primitive) x (J x v) (J x w) =
      evalTwo (M.exteriorDerivative reference.primitive) x v w
  g : Bundle.ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent
  metric_eq : ∀ x v w, g.inner x v w =
    evalTwo (M.exteriorDerivative reference.primitive) x v (J x w)

namespace CompatibleStructure
variable {d : ℕ} {M : SmoothManifold d} {reference : ExactSymplecticStructure M}

/-- A fiber synonym with the g norm, separate from the chart norm. -/
def MetricTangent (_A : CompatibleStructure reference) (x : M.Point) := M.Tangent x
instance (A : CompatibleStructure reference) (x : M.Point) :
    AddCommGroup (A.MetricTangent x) := inferInstanceAs (AddCommGroup (M.Tangent x))
instance (A : CompatibleStructure reference) (x : M.Point) :
    Module ℝ (A.MetricTangent x) := inferInstanceAs (Module ℝ (M.Tangent x))
instance (A : CompatibleStructure reference) (x : M.Point) :
    FiniteDimensional ℝ (A.MetricTangent x) :=
  inferInstanceAs (FiniteDimensional ℝ (M.Tangent x))
instance metricCore (A : CompatibleStructure reference) (x : M.Point) :
    InnerProductSpace.Core ℝ (A.MetricTangent x) := A.g.toRiemannianMetric.toCore x
instance (A : CompatibleStructure reference) (x : M.Point) :
    NormedAddCommGroup (A.MetricTangent x) := (A.metricCore x).toNormedAddCommGroup
instance (A : CompatibleStructure reference) (x : M.Point) :
    NormedSpace ℝ (A.MetricTangent x) := InnerProductSpace.Core.toNormedSpace

/-- The tangent norm is literally sqrt(dβ(v,Jv)). -/
theorem tangent_norm_eq (A : CompatibleStructure reference) (x : M.Point)
    (v : A.MetricTangent x) :
    ‖v‖ = Real.sqrt (evalTwo (M.exteriorDerivative reference.primitive) x v (A.J x v)) := by
  change Real.sqrt (A.g.inner x v v) = _
  exact congrArg Real.sqrt (A.metric_eq x v v)

abbrev Dual (A : CompatibleStructure reference) (x : M.Point) :=
  A.MetricTangent x →L[ℝ] ℝ

/-- Transfer a native covector to the same vector space with its g norm.
Finite dimensionality proves continuity; the map itself is unchanged. -/
def covector (A : CompatibleStructure reference) (x : M.Point)
    (l : M.Tangent x →L[ℝ] ℝ) : A.Dual x :=
  (show A.MetricTangent x →ₗ[ℝ] ℝ from l.toLinearMap).toContinuousLinearMap

theorem covector_apply (A : CompatibleStructure reference) (x : M.Point)
    (l : M.Tangent x →L[ℝ] ℝ) (v : A.MetricTangent x) : A.covector x l v = l v := rfl

def dualNorm (A : CompatibleStructure reference) (x : M.Point)
    (l : M.Tangent x →L[ℝ] ℝ) : ℝ := ‖A.covector x l‖

private theorem update_pair {E : Type*} (v w z : E) :
    Function.update ![v, w] (1 : Fin 2) z = ![v, z] := by
  ext i
  fin_cases i <;> simp

/-- Positive contraction, constructed from the actual alternating two-form. -/
def flatLinear (A : CompatibleStructure reference) (eta : M.Form 2) (x : M.Point) :
    A.MetricTangent x →ₗ[ℝ] Module.Dual ℝ (A.MetricTangent x) :=
  LinearMap.mk₂ ℝ (fun v w => evalTwo eta x v w)
    (by intros; exact (eta x).map_vecCons_add _ _ _)
    (by intros; exact (eta x).map_vecCons_smul _ _ _)
    (by
      intro v w z
      change M.Tangent x at v w z
      have h := (eta x).toContinuousMultilinearMap.map_update_add ![v, 0] 1 w z
      simp only [update_pair] at h
      exact h)
    (by
      intro c v w
      change M.Tangent x at v w
      have h := (eta x).toContinuousMultilinearMap.map_update_smul ![v, 0] 1 c w
      simp only [update_pair] at h
      exact h)

theorem flatLinear_injective (A : CompatibleStructure reference) (eta : M.Form 2)
    (x : M.Point) (h : M.Nondegenerate eta x) : Function.Injective (A.flatLinear eta x) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  apply h v
  intro w
  exact congrArg (fun l => l w) hv

/-- No inverse is assumed: nondegeneracy and finite dimension construct it. -/
def flatEquiv (A : CompatibleStructure reference) (eta : M.Form 2) (x : M.Point)
    (h : M.Nondegenerate eta x) :
    A.MetricTangent x ≃ₗ[ℝ] Module.Dual ℝ (A.MetricTangent x) :=
  LinearMap.linearEquivOfInjective (A.flatLinear eta x) (A.flatLinear_injective eta x h)
    Subspace.dual_finrank_eq.symm

def inverseContraction (A : CompatibleStructure reference) (eta : M.Form 2) (x : M.Point)
    (h : M.Nondegenerate eta x) : A.Dual x →L[ℝ] A.MetricTangent x :=
  ((A.flatEquiv eta x h).symm.toLinearMap.comp
    (show A.Dual x →ₗ[ℝ] Module.Dual ℝ (A.MetricTangent x) from
    { toFun := fun l : A.Dual x => l.toLinearMap
      map_add' := by intros; rfl
      map_smul' := by intros; rfl })).toContinuousLinearMap

theorem inverseContraction_equation (A : CompatibleStructure reference) (eta : M.Form 2)
    (x : M.Point) (h : M.Nondegenerate eta x) (l : A.Dual x) (w : A.MetricTangent x) :
    evalTwo eta x (A.inverseContraction eta x h l) w = l w := by
  exact congrArg (fun f => f w) ((A.flatEquiv eta x h).apply_symm_apply l.toLinearMap)

def inverseNorm (A : CompatibleStructure reference) (S : ExactSymplecticStructure M)
    (x : M.Point) : ℝ :=
  ‖A.inverseContraction (M.exteriorDerivative S.primitive) x (S.symplectic.2.2 x (mem_univ x))‖
end CompatibleStructure

/-- Smooth isotopy on the closed parameter interval, with actual diffeomorphisms. -/
def SmoothlyIsotopicToIdentity {d : ℕ} (M : SmoothManifold d) (F : M.SmoothEquiv M) : Prop :=
  ∃ H : ℝ → M.SmoothEquiv M,
    (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F x) ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) (𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × M.Point => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) (𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × M.Point => (H p.1).symm p.2) (Icc (0 : ℝ) 1 ×ˢ univ)

/-- Exact comparison is a conclusion, never an input field. -/
def ExactComparison {d : ℕ} (M : SmoothManifold d) (source target : M.Form 1) : Prop :=
  ∃ F : M.SmoothEquiv M, SmoothlyIsotopicToIdentity M F ∧
    ∃ h : M.Point → ℝ, ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ h ∧
      (∀ x v, evalOne (M.pullback M F source) x v =
        evalOne target x v + M.scalarDerivative h x v) ∧
      M.pullback M F (M.exteriorDerivative source) = M.exteriorDerivative target

end ExactLiouvilleComparison
