import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationFrames
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationBundleCoordinates

/-! Smooth compatible normalization on a native finite-dimensional real vector bundle. -/
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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- A frame is used only to define the formula; the result is frame-independent. -/
def normalizationFrame (x : B) : E x ≃L[ℝ] Vec (Module.finrank ℝ F) :=
  ((trivializationAt F E x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt F E x)).trans (Module.finBasis ℝ F).equivFunL

/-- Explicit normalization of the supplied metric and symplectic form. -/
def normalizedEndomorphism (omega : SymplecticForm IB F E)
    (h : ContMDiffRiemannianMetric IB ∞ F E) (x : B) : E x →L[ℝ] E x :=
  normalizeIn (normalizationFrame (F := F) x) (h.inner x) (omega.form x)

theorem normalizedEndomorphism_compatible (omega : SymplecticForm IB F E)
    (h : ContMDiffRiemannianMetric IB ∞ F E) (x : B) :
    Compatible (omega.form x) (normalizedEndomorphism omega h x) :=
  normalizeIn_compatible _ _ _ (h.symm x) (h.pos x)
    (omega.alternating x) (omega.nondegenerate x)

theorem normalizedEndomorphism_recovery (omega : SymplecticForm IB F E)
    (h : ContMDiffRiemannianMetric IB ∞ F E) (x : B) (J₀ : E x →L[ℝ] E x)
    (hJ : Compatible (omega.form x) J₀)
    (heq : ∀ v w, h.inner x v w = omega.form x v (J₀ w)) :
    normalizedEndomorphism omega h x = J₀ :=
  normalizeIn_recovery _ _ _ (h.symm x) (h.pos x) J₀ hJ.1 heq

/-- The global formula agrees with any frame, not just the chosen covering chart. -/
theorem normalizedEndomorphism_eq_frame (omega : SymplecticForm IB F E)
    (h : ContMDiffRiemannianMetric IB ∞ F E) (x : B)
    (e : E x ≃L[ℝ] Vec (Module.finrank ℝ F)) :
    normalizedEndomorphism omega h x = normalizeIn e (h.inner x) (omega.form x) :=
  normalizeIn_frame_independent _ _ _ _ (h.symm x) (h.pos x)
    (omega.alternating x) (omega.nondegenerate x)

theorem normalizedEndomorphism_contMDiff [IsManifold IB ∞ B]
    [ContMDiffVectorBundle ∞ F E IB] (omega : SymplecticForm IB F E)
    (h : ContMDiffRiemannianMetric IB ∞ F E) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) x (normalizedEndomorphism omega h x)) := by
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  let q := (Module.finBasis ℝ F).equivFunL
  let s := (trivializationAt F E x).baseSet
  have hx : x ∈ s := mem_baseSet_trivializationAt F E x
  have hs : s ∈ 𝓝 x := (trivializationAt F E x).open_baseSet.mem_nhds hx
  let G := fun y ↦ matrixIn q (bilinearCoordinates (F := F) x y (h.inner y))
  let W := fun y ↦ matrixIn q (bilinearCoordinates (F := F) x y (omega.form y))
  have hG : ContMDiffAt IB 𝓘(ℝ, Mat (Module.finrank ℝ F)) ∞ G x :=
    contMDiffAt_matrixIn q (contMDiffAt_bilinearCoordinates _ h.contMDiff x)
  have hW : ContMDiffAt IB 𝓘(ℝ, Mat (Module.finrank ℝ F)) ∞ W x :=
    contMDiffAt_matrixIn q (contMDiffAt_bilinearCoordinates _ omega.smooth x)
  have hp : ∀ y ∈ s, (G y).PosDef := by
    intro y hy
    dsimp only [G]
    rw [matrixIn_bilinearCoordinates q x y hy]
    exact matrixIn_posDef _ _ (h.symm y) (h.pos y)
  have ha : ∀ y ∈ s, (W y).transpose = -(W y) := by
    intro y hy
    dsimp only [W]
    rw [matrixIn_bilinearCoordinates q x y hy]
    exact matrixIn_skew _ _ (omega.alternating y)
  have hu : ∀ y ∈ s, IsUnit (W y) := by
    intro y hy
    dsimp only [W]
    rw [matrixIn_bilinearCoordinates q x y hy]
    exact matrixIn_isUnit _ _ (omega.alternating y) (omega.nondegenerate y)
  have hN := (contMDiffWithinAt_normalize hx hG.contMDiffWithinAt
    hW.contMDiffWithinAt hp ha hu).contMDiffAt hs
  apply (contMDiffAt_endomorphismIn q hN).congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  rw [normalizedEndomorphism_eq_frame omega h y
    (((trivializationAt F E x).continuousLinearEquivAt ℝ y hy).trans q)]
  dsimp only [normalizeIn]
  rw [endomorphismIn_coordinates q x y hy]
  dsimp only [G, W]
  rw [matrixIn_bilinearCoordinates q x y hy, matrixIn_bilinearCoordinates q x y hy]

/-- Native smooth compatible normalization, including every finite rank and empty base. -/
theorem normalization [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F E IB]
    (omega : SymplecticForm IB F E) (h : ContMDiffRiemannianMetric IB ∞ F E) :
    NormalizationTarget IB F E omega h :=
  ⟨normalizedEndomorphism omega h, normalizedEndomorphism_contMDiff omega h,
    normalizedEndomorphism_compatible omega h, normalizedEndomorphism_recovery omega h⟩

end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
