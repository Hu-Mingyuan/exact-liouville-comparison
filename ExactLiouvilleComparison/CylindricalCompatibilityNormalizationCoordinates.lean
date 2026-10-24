import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationRegularity
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationStatement
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-! Fixed-frame native continuous-linear coordinate operations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open Bundle Matrix
open scoped Manifold ContDiff MatrixOrder Matrix.Norms.L2Operator

namespace ExactLiouvilleComparison.CylindricalCompatibility.Normalization
open NormalizationAlgebra

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual coefficients of a continuous bilinear form in a continuous frame. -/
def matrixIn (e : V ≃L[ℝ] Vec n) (A : V →L[ℝ] V →L[ℝ] ℝ) : Mat n :=
  (A.toBilinForm.comp e.symm.toLinearMap e.symm.toLinearMap).toMatrix'

@[simp] theorem matrixIn_apply (e : V ≃L[ℝ] Vec n)
    (A : V →L[ℝ] V →L[ℝ] ℝ) (i j : Fin n) :
    matrixIn e A i j = A (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) := rfl

@[simp] theorem form_matrixIn (e : V ≃L[ℝ] Vec n)
    (A : V →L[ℝ] V →L[ℝ] ℝ) (v w : Vec n) :
    form (matrixIn e A) v w = A (e.symm v) (e.symm w) := by
  simp [matrixIn, form]

/-- The ordinary matrix action, realized as a native continuous linear map. -/
def matrixEndL : Mat n →L[ℝ] (Vec n →L[ℝ] Vec n) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toLin'.toLinearMap).toContinuousLinearMap

@[simp] theorem matrixEndL_apply (T : Mat n) (v : Vec n) :
    matrixEndL T v = T *ᵥ v := rfl

/-- Transport the matrix action back to the actual fiber. -/
def endomorphismIn (e : V ≃L[ℝ] Vec n) (T : Mat n) : V →L[ℝ] V :=
  e.symm.toContinuousLinearMap.comp ((matrixEndL T).comp e.toContinuousLinearMap)

@[simp] theorem endomorphismIn_apply (e : V ≃L[ℝ] Vec n) (T : Mat n) (v : V) :
    endomorphismIn e T v = e.symm (T *ᵥ e v) := rfl

/-- Taking matrix coefficients is itself a continuous linear operation. -/
def matrixInL (e : V ≃L[ℝ] Vec n) : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] Mat n where
  toFun := matrixIn e
  map_add' := by intro A B; ext i j; rfl
  map_smul' := by intro c A; ext i j; rfl
  cont := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_id.clm_apply continuous_const).clm_apply continuous_const

@[simp] theorem matrixInL_apply (e : V ≃L[ℝ] Vec n) (A : V →L[ℝ] V →L[ℝ] ℝ) :
    matrixInL e A = matrixIn e A := rfl

/-- Back-transport of matrices is continuous linear for a fixed frame. -/
def endomorphismInL (e : V ≃L[ℝ] Vec n) : Mat n →L[ℝ] (V →L[ℝ] V) :=
  (e.symm.arrowCongr e.symm).toContinuousLinearMap.comp matrixEndL

@[simp] theorem endomorphismInL_apply (e : V ≃L[ℝ] Vec n) (T : Mat n) :
    endomorphismInL e T = endomorphismIn e T := by
  ext v
  rfl

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {s : Set B} {x : B}

theorem contMDiffAt_matrixIn (e : V ≃L[ℝ] Vec n)
    {A : B → V →L[ℝ] V →L[ℝ] ℝ}
    (hA : ContMDiffAt IB 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ∞ A x) :
    ContMDiffAt IB 𝓘(ℝ, Mat n) ∞ (fun y ↦ matrixIn e (A y)) x :=
  (matrixInL e).contDiff.contDiffAt.comp_contMDiffAt hA

theorem contMDiffAt_endomorphismIn (e : V ≃L[ℝ] Vec n) {T : B → Mat n}
    (hT : ContMDiffAt IB 𝓘(ℝ, Mat n) ∞ T x) :
    ContMDiffAt IB 𝓘(ℝ, V →L[ℝ] V) ∞ (fun y ↦ endomorphismIn e (T y)) x := by
  simpa only [Function.comp_def, endomorphismInL_apply] using
    (endomorphismInL e).contDiff.contDiffAt.comp_contMDiffAt hT

end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
