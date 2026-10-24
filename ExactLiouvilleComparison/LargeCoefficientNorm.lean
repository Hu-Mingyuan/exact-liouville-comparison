import ExactLiouvilleComparison.Statement
import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-! The primitive norm is the accepted explicit metric dual norm. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.LargeCoefficient
variable {d : ℕ} {M : SmoothManifold d} {S : ExactSymplecticStructure M}

def oneCovector (lam : M.Form 1) (x : M.Point) : M.Tangent x →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ (M.Tangent x) ℝ (0 : Fin 1)).symm (lam x)

theorem oneCovector_apply (lam : M.Form 1) (x : M.Point) (v : M.Tangent x) :
    oneCovector lam x v = evalOne lam x v := rfl

def formNorm (A : CompatibleStructure S) (lam : M.Form 1) (x : M.Point) : ℝ :=
  A.dualNorm x (oneCovector lam x)

theorem formNorm_nonneg (A : CompatibleStructure S) (lam : M.Form 1) (x : M.Point) :
    0 ≤ formNorm A lam x := norm_nonneg _

theorem formNorm_locally_bounded (A : CompatibleStructure S) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (x : M.Point) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, formNorm A lam y ≤ C := by
  let g := A.g.toRiemannianMetric
  -- These native instances preserve the original tangent topology. Their norm
  -- is the very same sqrt(g(v,v)) as the accepted MetricTangent norm (hnorm below).
  letI ng : ∀ y, NormedAddCommGroup (M.Tangent y) := fun y =>
    (g.toCore y).toNormedAddCommGroupOfTopology (g.continuousAt y) (g.isVonNBounded y)
  letI ig : ∀ y, InnerProductSpace ℝ (M.Tangent y) := fun y =>
    .ofCoreOfTopology (g.toCore y) (g.continuousAt y) (g.isVonNBounded y)
  letI : IsContinuousRiemannianBundle (Model d) M.Tangent :=
    ⟨A.g.inner, A.g.contMDiff.continuous, fun _ _ _ => rfl⟩
  obtain ⟨C, hC, hb⟩ := eventually_norm_trivializationAt_lt (Model d) M.Tangent x
  let f := fun y => M.formInChart x lam (chartAt (Model d) x y)
  have hf : ContinuousAt f x :=
    ((hlam x).continuousOn.continuousAt (chart_target_mem_nhds (Model d) x)).comp
      ((chartAt (Model d) x).continuousAt (mem_chart_source _ _))
  have hfn : ∀ᶠ y in 𝓝 x, ‖f y‖ < ‖f x‖ + 1 :=
    hf.norm.eventually (eventually_lt_nhds (by linarith))
  refine ⟨(‖f x‖ + 1) * C, mul_nonneg (by positivity) hC.le, ?_⟩
  filter_upwards [hb, hfn, chart_source_mem_nhds (Model d) x] with y hy hfy hys
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hC.le)
  intro v
  have hrecon := congrArg (fun q : M.Tangent y [⋀^Fin 1]→L[ℝ] ℝ => q (fun _ => v))
    (M.formInChart_comp_chartTangentMap lam x y hys)
  have ht : (trivializationAt (Model d) M.Tangent x).continuousLinearMapAt ℝ y =
      M.chartTangentMap x y := by
    simpa only [chartTangentMap, extChartAt_coe,
      modelWithCornersSelf_coe, Function.id_comp] using
      (TangentBundle.continuousLinearMapAt_trivializationAt
        (I := 𝓘(ℝ, Model d)) hys)
  have hn := (f y).toContinuousMultilinearMap.le_opNorm (fun _ : Fin 1 =>
    (trivializationAt (Model d) M.Tangent x).continuousLinearMapAt ℝ y v)
  simp only [Fin.prod_univ_one] at hn
  have htv := ((trivializationAt (Model d) M.Tangent x).continuousLinearMapAt ℝ y).le_opNorm v
  have hnorm : @norm (M.Tangent y) (ng y).toNorm v =
      @norm (A.MetricTangent y) (inferInstance : Norm (A.MetricTangent y)) v := rfl
  change ‖lam y (fun _ => v)‖ ≤ _
  have heval : lam y (fun _ => v) = f y (fun _ =>
      (trivializationAt (Model d) M.Tangent x).continuousLinearMapAt ℝ y v) := by
    rw [ht]
    exact hrecon.symm
  rw [heval]
  calc
    _ ≤ ‖f y‖ * ‖(trivializationAt (Model d) M.Tangent x).continuousLinearMapAt ℝ y v‖ := hn
    _ ≤ ‖f y‖ * (C * ‖v‖) := mul_le_mul_of_nonneg_left
      (htv.trans (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))) (norm_nonneg _)
    _ ≤ (‖f x‖ + 1) * C * ‖v‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hfy.le (mul_nonneg hC.le (norm_nonneg _))
    _ = _ := congrArg (fun t : ℝ => (‖f x‖ + 1) * C * t) hnorm

theorem formNorm_bddAbove_on_compact (A : CompatibleStructure S) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) {K : Set M.Point} (hK : IsCompact K) :
    BddAbove (formNorm A lam '' K) := by
  apply Bornology.IsBounded.bddAbove
  apply Bornology.isBounded_image_of_isLocallyBounded_of_isCompact hK
  intro x
  obtain ⟨C, hC, hb⟩ := formNorm_locally_bounded A lam hlam x
  refine ⟨{y | formNorm A lam y ≤ C}, hb, ?_⟩
  apply (isCompact_Icc (a := (0 : ℝ)) (b := C)).isBounded.subset
  rintro z ⟨y, hy, rfl⟩
  exact ⟨formNorm_nonneg A lam y, hy⟩

end ExactLiouvilleComparison.LargeCoefficient
