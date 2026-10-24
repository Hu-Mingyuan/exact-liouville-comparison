import ExactLiouvilleComparison.SteinReferenceStatement
import FsFltz.Geometry.SmoothForms
import FsFltz.Geometry.LiouvilleFlowPrimitive
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual standard primitive and its unnormalized exterior derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.SteinReferenceConstruction

abbrev Ambient (N : ℕ) := EuclideanSpace ℂ (Fin N)

def complexStructure (N : ℕ) : Ambient N →L[ℝ] Ambient N :=
  (Complex.I • ContinuousLinearMap.id ℂ (Ambient N)).restrictScalars ℝ

@[simp] theorem complexStructure_apply {N : ℕ} (v : Ambient N) :
    complexStructure N v = Complex.I • v := rfl

/-- The real Euclidean inner product, with its actual inferred PiL2 instance. -/
theorem ambient_inner_I_swap {N : ℕ} (v w : Ambient N) :
    inner ℝ w (Complex.I • v) = -inner ℝ v (Complex.I • w) := by
  simp only [PiLp.inner_apply]
  change (∑ j : Fin N, inner ℝ (w j) (Complex.I * v j)) =
    -(∑ j : Fin N, inner ℝ (v j) (Complex.I * w j))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

/-- A continuous linear family of covectors, beta_z(v)=-inner(z,Iv)/2. -/
def ambientCovector (N : ℕ) : Ambient N →L[ℝ] Ambient N →L[ℝ] ℝ :=
  -(1 / 2 : ℝ) • ((ContinuousLinearMap.compL ℝ (Ambient N) (Ambient N) ℝ).flip
    (complexStructure N)).comp (innerSL ℝ)

@[simp] theorem ambientCovector_apply {N : ℕ} (z v : Ambient N) :
    ambientCovector N z v = -(1 / 2 : ℝ) * inner ℝ z (Complex.I • v) := rfl

def ambientPrimitive (N : ℕ) : Ambient N →L[ℝ] Ambient N [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Ambient N)
    (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ambientCovector N)

@[simp] theorem ambientPrimitive_apply {N : ℕ} (z : Ambient N) (v : Fin 1 → Ambient N) :
    ambientPrimitive N z v = -(1 / 2 : ℝ) * inner ℝ z (Complex.I • v 0) := rfl

theorem ambient_exteriorDerivative {N : ℕ} (z v w : Ambient N) :
    extDeriv (ambientPrimitive N) z ![v,w] = -inner ℝ v (Complex.I • w) := by
  rw [LiouvilleFlowPrimitive.extDeriv_one_apply, (ambientPrimitive N).fderiv]
  simp only [ambientPrimitive_apply, ambient_inner_I_swap v w]
  ring

end ExactLiouvilleComparison.SteinReferenceConstruction
