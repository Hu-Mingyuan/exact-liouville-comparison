import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationSqrt
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebra
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Native manifold composition for the literal matrix normalization formula.
The polar square is positive by the proved finite-dimensional algebra. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff MatrixOrder Matrix.Norms.L2Operator

namespace ExactLiouvilleComparison.CylindricalCompatibility.Normalization

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {n : ℕ} {s : Set B}

local instance : ContMDiffMul 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
    (NormalizationAlgebra.Mat n) := by
  constructor
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact contDiff_mul.contMDiff

theorem contMDiffOn_sqrt_comp {f : B → NormalizationAlgebra.Mat n}
    (hf : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ f s)
    (hp : ∀ x ∈ s, (f x).PosDef) :
    ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ (fun x ↦ CFC.sqrt (f x)) s :=
  NormalizationSqrt.contDiffOn_sqrt_posDef.contMDiffOn.comp hf hp

theorem contMDiffOn_inv_sqrt_comp {f : B → NormalizationAlgebra.Mat n}
    (hf : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ f s)
    (hp : ∀ x ∈ s, (f x).PosDef) :
    ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun x ↦ (CFC.sqrt (f x))⁻¹) s := by
  have hi := NormalizationSqrt.contDiffOn_inverse_sqrt_comp
    (contDiff_id.contDiffOn : ContDiffOn ℝ ∞ (id : NormalizationAlgebra.Mat n → _)
      {A | A.PosDef}) (fun _ h ↦ h)
  simpa only [id_eq, Matrix.nonsing_inv_eq_ringInverse] using! hi.contMDiffOn.comp hf hp

theorem contMDiffOn_skew {G W : B → NormalizationAlgebra.Mat n}
    (hG : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ G s)
    (hW : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ W s)
    (hp : ∀ x ∈ s, (G x).PosDef) :
    ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun x ↦ NormalizationAlgebra.skew (G x) (W x)) s := by
  exact ((contMDiffOn_inv_sqrt_comp hG hp).neg.mul hW).mul
    (contMDiffOn_inv_sqrt_comp hG hp)

theorem contMDiffOn_normalize_of_posDef {G W : B → NormalizationAlgebra.Mat n}
    (hG : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ G s)
    (hW : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ W s)
    (hp : ∀ x ∈ s, (G x).PosDef)
    (hq : ∀ x ∈ s, (-(NormalizationAlgebra.skew (G x) (W x) *
      NormalizationAlgebra.skew (G x) (W x))).PosDef) :
    ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun x ↦ NormalizationAlgebra.normalize (G x) (W x)) s := by
  have hK := contMDiffOn_skew hG hW hp
  exact (((contMDiffOn_inv_sqrt_comp hG hp).mul hK).mul
    (contMDiffOn_inv_sqrt_comp (hK.mul hK).neg hq)).mul (contMDiffOn_sqrt_comp hG hp)

/-- Smoothness of the actual normalizer, with only the metric and symplectic hypotheses. -/
theorem contMDiffOn_normalize {G W : B → NormalizationAlgebra.Mat n}
    (hG : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ G s)
    (hW : ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ W s)
    (hp : ∀ x ∈ s, (G x).PosDef)
    (ha : ∀ x ∈ s, (W x).transpose = -(W x))
    (hu : ∀ x ∈ s, IsUnit (W x)) :
    ContMDiffOn IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun x ↦ NormalizationAlgebra.normalize (G x) (W x)) s := by
  apply contMDiffOn_normalize_of_posDef hG hW hp
  intro x hx
  exact NormalizationAlgebra.neg_sq_posDef
    (NormalizationAlgebra.skew_transpose (hp x hx) (ha x hx))
    (NormalizationAlgebra.skew_unit (hp x hx) (hu x hx))

/-- Local composition needs positivity only on a neighborhood of the base point. -/
theorem contMDiffWithinAt_sqrt_comp {x : B} (hx : x ∈ s)
    {f : B → NormalizationAlgebra.Mat n}
    (hf : ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ f s x)
    (hp : ∀ y ∈ s, (f y).PosDef) :
    ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun y ↦ CFC.sqrt (f y)) s x :=
  (NormalizationSqrt.contDiffOn_sqrt_posDef.contMDiffOn _ (hp x hx)).comp x hf hp

theorem contMDiffWithinAt_inv_sqrt_comp {x : B} (hx : x ∈ s)
    {f : B → NormalizationAlgebra.Mat n}
    (hf : ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ f s x)
    (hp : ∀ y ∈ s, (f y).PosDef) :
    ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun y ↦ (CFC.sqrt (f y))⁻¹) s x := by
  have hi := NormalizationSqrt.contDiffOn_inverse_sqrt_comp
    (contDiff_id.contDiffOn : ContDiffOn ℝ ∞ (id : NormalizationAlgebra.Mat n → _)
      {A | A.PosDef}) (fun _ h ↦ h)
  simpa only [id_eq, Matrix.nonsing_inv_eq_ringInverse] using!
    (hi.contMDiffOn _ (hp x hx)).comp x hf hp

theorem contMDiffWithinAt_normalize {x : B} (hx : x ∈ s)
    {G W : B → NormalizationAlgebra.Mat n}
    (hG : ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ G s x)
    (hW : ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞ W s x)
    (hp : ∀ y ∈ s, (G y).PosDef)
    (ha : ∀ y ∈ s, (W y).transpose = -(W y))
    (hu : ∀ y ∈ s, IsUnit (W y)) :
    ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun y ↦ NormalizationAlgebra.normalize (G y) (W y)) s x := by
  have hi := contMDiffWithinAt_inv_sqrt_comp hx hG hp
  have hK : ContMDiffWithinAt IB 𝓘(ℝ, NormalizationAlgebra.Mat n) ∞
      (fun y ↦ NormalizationAlgebra.skew (G y) (W y)) s x :=
    (hi.neg.mul hW).mul hi
  have hq : ∀ y ∈ s, (-(NormalizationAlgebra.skew (G y) (W y) *
      NormalizationAlgebra.skew (G y) (W y))).PosDef := by
    intro y hy
    exact NormalizationAlgebra.neg_sq_posDef
      (NormalizationAlgebra.skew_transpose (hp y hy) (ha y hy))
      (NormalizationAlgebra.skew_unit (hp y hy) (hu y hy))
  exact ((hi.mul hK).mul
    (contMDiffWithinAt_inv_sqrt_comp hx (hK.mul hK).neg hq)).mul
      (contMDiffWithinAt_sqrt_comp hx hG hp)

end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
