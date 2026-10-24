import ExactLiouvilleComparison.SteinReferenceMetricStatement
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The native smooth metric induced by an immersion into a real inner-product space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry Set Filter Bundle

namespace ExactLiouvilleComparison.SteinReferenceMetric

/-- Injectivity in finite source dimension makes the pullback unit ball bounded
in the preexisting topology, including when the source is zero-dimensional. -/
theorem pullback_unitBall_bounded {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Injective L) :
    Bornology.IsVonNBounded ℝ {v : E | inner ℝ (L v) (L v) < 1} := by
  obtain ⟨K, _, hK⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hL
  rw [NormedSpace.isVonNBounded_iff]
  apply (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : F)) (r := 1))).subset
  intro v hv
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
  change ‖L v‖ < 1
  rw [mem_ofPred_eq, real_inner_self_eq_norm_sq] at hv
  nlinarith [norm_nonneg (L v)]

variable {d : ℕ} (M : SmoothManifold d)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The continuous bilinear pullback of the real ambient inner product.
The temporary model norm is used only to construct continuous bilinear maps;
its topology is definitionally the original tangent-fiber topology. -/
def metricBilin (f : M.Point → F) (x : M.Point) :
    M.Tangent x →L[ℝ] M.Tangent x →L[ℝ] ℝ := by
  letI : NormedAddCommGroup (M.Tangent x) := inferInstanceAs (NormedAddCommGroup (Model d))
  letI : NormedSpace ℝ (M.Tangent x) := inferInstanceAs (NormedSpace ℝ (Model d))
  let L : M.Tangent x →L[ℝ] F := mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x
  exact (innerSL ℝ).bilinearComp L L

@[simp] theorem metricBilin_apply (f : M.Point → F) (x : M.Point) (v w : M.Tangent x) :
    metricBilin M f x v w = @inner ℝ F _
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x v)
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x w) := rfl

/-- Native derivative coefficients in a fixed source tangent trivialization
are smooth. The ambient tangent trivialization is the canonical identity. -/
theorem smooth_derivative_coordinates (f : M.Point → F)
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) ∞ f) (x : M.Point) :
    ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d →L[ℝ] F)) ∞
      (fun y => (show M.Tangent y →L[ℝ] F from
        mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f y).comp
          ((trivializationAt (Model d) M.Tangent x).symmL ℝ y)) x := by
  have h := (hf x).mfderiv_const (m := ∞) (by simp)
  convert! h using 1
  ext y v
  simp [_root_.inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_apply]
  rfl

/-- Smoothness is in the native bilinear-map bundle over the tangent bundle. -/
theorem smooth_metricBilin (f : M.Point → F)
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) ∞ f) :
    ContMDiff (𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d →L[ℝ] Model d →L[ℝ] ℝ))) ∞
      (fun x => TotalSpace.mk' (Model d →L[ℝ] Model d →L[ℝ] ℝ) x
        (metricBilin M f x)) := by
  intro x
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  have hD := smooth_derivative_coordinates M f hf x
  let B : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  have hconst : ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun _ : M.Point => B) x := contMDiffAt_const
  have hinner := hconst.clm_comp hD
  have hB := (hD.clm_precomp (F₃ := ℝ)).clm_comp hinner
  apply hB.congr_of_eventuallyEq
  filter_upwards [(trivializationAt (Model d) M.Tangent x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt (Model d) M.Tangent x)] with y hy
  ext v w
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp [metricBilin_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  change @inner ℝ F _
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f y
        ((trivializationAt (Model d) M.Tangent x).symm y v))
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f y
        ((trivializationAt (Model d) M.Tangent x).symm y w)) = _
  rw [← (trivializationAt (Model d) M.Tangent x).symmL_apply (R := ℝ) hy v,
    ← (trivializationAt (Model d) M.Tangent x).symmL_apply (R := ℝ) hy w]
  rfl

/-- Construct the native induced smooth metric from only smoothness and
injectivity of the native derivative. No metric data are supplied. -/
def ofImmersion [FiniteDimensional ℝ F] (f : M.Point → F)
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x)) :
    ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent where
  inner := metricBilin M f
  symm x v w := real_inner_comm _ _
  pos x v hv := by
    rw [metricBilin_apply]
    let L : M.Tangent x →L[ℝ] F := mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x
    have hL : Function.Injective L := hinj x
    exact real_inner_self_pos.mpr (fun hz => hv (hL (hz.trans L.map_zero.symm)))
  isVonNBounded x := by
    let : NormedAddCommGroup (M.Tangent x) := inferInstanceAs (NormedAddCommGroup (Model d))
    let : NormedSpace ℝ (M.Tangent x) := inferInstanceAs (NormedSpace ℝ (Model d))
    exact pullback_unitBall_bounded
      (show M.Tangent x →L[ℝ] F from mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x) (hinj x)
  contMDiff := smooth_metricBilin M f hf

@[simp] theorem ofImmersion_inner [FiniteDimensional ℝ F] (f : M.Point → F)
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x))
    (x : M.Point) (v w : M.Tangent x) :
    (ofImmersion M f hf hinj).inner x v w = @inner ℝ F _
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x v)
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, F)) f x w) := rfl

variable {M}

/-- Specialization using exactly the original proper complex embedding data. -/
def metric {N : ℕ} (i : ProperComplexEmbedding M N) :
    ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent :=
  ofImmersion M i.map i.smooth i.immersion

/-- Literally the metric identity required by `SteinReference.induced_metric`. -/
@[simp] theorem metric_inner {N : ℕ} (i : ProperComplexEmbedding M N)
    (x : M.Point) (v w : M.Tangent x) :
    (metric i).inner x v w = @inner ℝ (EuclideanSpace ℂ (Fin N)) _
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x w) := rfl

theorem smoothImmersionMetricTarget : SmoothImmersionMetricTarget := by
  intro d M F _ _ _ f hf hinj
  exact ⟨ofImmersion M f hf hinj, ofImmersion_inner M f hf hinj⟩

theorem properComplexMetricTarget : ProperComplexMetricTarget := by
  intro d N M i
  exact ⟨metric i, metric_inner i⟩

end ExactLiouvilleComparison.SteinReferenceMetric
