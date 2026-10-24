import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationCoordinates

/-! Native bilinear bundle coordinates used in normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology MatrixOrder Matrix.Norms.L2Operator

namespace ExactLiouvilleComparison.CylindricalCompatibility.Normalization
open NormalizationAlgebra

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The native local representative of a bilinear section in the chart at `x`. -/
def bilinearCoordinates (x y : B) (A : E y →L[ℝ] E y →L[ℝ] ℝ) :
    F →L[ℝ] F →L[ℝ] ℝ :=
  inCoordinates F E (F →L[ℝ] ℝ) (fun z ↦ E z →L[ℝ] ℝ) x y x y A

lemma bilinearCoordinates_apply (x y : B)
    (hy : y ∈ (trivializationAt F E x).baseSet)
    (A : E y →L[ℝ] E y →L[ℝ] ℝ) (v w : F) :
    bilinearCoordinates x y A v w =
      A (((trivializationAt F E x).continuousLinearEquivAt ℝ y hy).symm v)
        (((trivializationAt F E x).continuousLinearEquivAt ℝ y hy).symm w) := by
  rw [bilinearCoordinates, inCoordinates_apply_eq₂ hy hy (by simp)]
  simp

lemma contMDiffAt_bilinearCoordinates
    (A : (y : B) → E y →L[ℝ] E y →L[ℝ] ℝ)
    (hA : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) y (A y))) (x : B) :
    ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun y ↦ bilinearCoordinates (F := F) x y (A y)) x :=
  ((contMDiffAt_hom_bundle _).mp (hA x)).2

lemma matrixIn_bilinearCoordinates {n : ℕ} (q : F ≃L[ℝ] Vec n)
    (x y : B) (hy : y ∈ (trivializationAt F E x).baseSet)
    (A : E y →L[ℝ] E y →L[ℝ] ℝ) :
    matrixIn q (bilinearCoordinates x y A) =
      matrixIn (((trivializationAt F E x).continuousLinearEquivAt ℝ y hy).trans q) A := by
  ext i j
  simp only [matrixIn_apply, bilinearCoordinates_apply x y hy]
  rfl

lemma endomorphismIn_coordinates {n : ℕ} (q : F ≃L[ℝ] Vec n)
    (x y : B) (hy : y ∈ (trivializationAt F E x).baseSet) (T : Mat n) :
    inCoordinates F E F E x y x y
      (endomorphismIn (((trivializationAt F E x).continuousLinearEquivAt ℝ y hy).trans q) T) =
      endomorphismIn q T := by
  rw [inCoordinates_eq hy hy]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    endomorphismIn_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.apply_symm_apply]

end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
