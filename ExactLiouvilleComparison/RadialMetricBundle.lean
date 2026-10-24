import ExactLiouvilleComparison.RadialMetric
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter Bundle
namespace ExactLiouvilleComparison
namespace RadialMetricBundle
variable {d : ℕ} (M : SmoothManifold d)

def SmoothCovector (l : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) : Prop :=
  ContMDiff (𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d →L[ℝ] ℝ))) ∞
    (fun x => Bundle.TotalSpace.mk' (Model d →L[ℝ] ℝ) x (l x))

theorem smooth_differential (R : M.Point → ℝ)
    (hR : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R) :
    SmoothCovector M (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) R) := by
  intro x
  rw [contMDiffAt_section]
  have h := (hR x).mfderiv_const (m := ∞) (by simp)
  simp only [hom_trivializationAt_apply]
  convert! h using 1
  ext y v
  simp [_root_.inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_apply]
  rfl

/-- Coordinate criterion for a native smooth covector section. -/
theorem smoothCovector_iff (l : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) :
    SmoothCovector M l ↔ ∀ x, ContMDiffAt (𝓘(ℝ, Model d))
      (𝓘(ℝ, Model d →L[ℝ] ℝ)) ∞
      (fun y => (l y).comp ((trivializationAt (Model d) M.Tangent x).symmL ℝ y)) x := by
  constructor <;> intro h x
  · have hx := h x
    simpa [contMDiffAt_section, hom_trivializationAt_apply,
      ContinuousLinearMap.inCoordinates] using hx
  · have hx := h x
    simpa [contMDiffAt_section, hom_trivializationAt_apply,
      ContinuousLinearMap.inCoordinates] using hx

/-- Smooth composition of a covector with a tangent endomorphism. -/
theorem smooth_comp (l : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hl : SmoothCovector M l)
    (J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x)
    (hJ : SmoothEndomorphism M J) : SmoothCovector M (fun x => (l x).comp (J x)) := by
  rw [smoothCovector_iff]
  intro x
  have hL := (smoothCovector_iff M l).1 hl x
  have hJx := hJ x
  rw [contMDiffAt_section] at hJx
  simp only [hom_trivializationAt_apply] at hJx
  apply (hL.clm_comp hJx).congr_of_eventuallyEq
  filter_upwards [(trivializationAt (Model d) M.Tangent x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt (Model d) M.Tangent x)] with y hy
  ext v
  change (l y) ((J y) (((trivializationAt (Model d) M.Tangent x).symmL ℝ y) v)) =
    (l y) (((trivializationAt (Model d) M.Tangent x).symmL ℝ y)
      (((trivializationAt (Model d) M.Tangent x).continuousLinearMapAt ℝ y)
        ((J y) (((trivializationAt (Model d) M.Tangent x).symmL ℝ y) v))))
  rw [Trivialization.symmL_continuousLinearMapAt _ hy]

/-- A covector square is a smooth native bilinear section. -/
theorem smooth_tensor (l : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hl : SmoothCovector M l) :
    ContMDiff (𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d →L[ℝ] Model d →L[ℝ] ℝ))) ∞
      (fun x => Bundle.TotalSpace.mk' (Model d →L[ℝ] Model d →L[ℝ] ℝ) x
        ((l x).smulRight (l x))) := by
  intro x
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  have hL := (smoothCovector_iff M l).1 hl x
  have hsm : ContDiff ℝ ∞ (fun p : (Model d →L[ℝ] ℝ) × (Model d →L[ℝ] ℝ) =>
      p.1.smulRight p.2) := contDiff_fst.smulRight contDiff_snd
  have hh := hsm.contDiffAt.comp_contMDiffAt (hL.prodMk_space hL)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(trivializationAt (Model d) M.Tangent x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt (Model d) M.Tangent x)] with y hy
  ext v w
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp [ContinuousLinearMap.smulRight_apply]
  change (l y) ((trivializationAt (Model d) M.Tangent x).symm y v) *
      (l y) ((trivializationAt (Model d) M.Tangent x).symm y w) =
    (l y) (((trivializationAt (Model d) M.Tangent x).symmL ℝ y) v) *
      (l y) (((trivializationAt (Model d) M.Tangent x).symmL ℝ y) w)
  exact congrArg₂ (fun a b : M.Tangent y => l y a * l y b)
    ((trivializationAt (Model d) M.Tangent x).symmL_apply hy v).symm
    ((trivializationAt (Model d) M.Tangent x).symmL_apply hy w).symm

end RadialMetricBundle
end ExactLiouvilleComparison
