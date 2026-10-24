import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAtlasLinear
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Atlas

variable {d : ℕ} (D : LiouvilleDomain d)

abbrev ambientChart (x : D.domain.boundary.Point) :=
  trivializationAt (Model (d - 1)) D.domain.boundary.Tangent x

def covector (y : D.domain.boundary.Point) : D.domain.boundary.Tangent y →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)).symm (boundaryAlpha D y)

def coefficient (x y : D.domain.boundary.Point) : Model (d - 1) →L[ℝ] ℝ :=
  (covector D y).comp ((ambientChart D x).symmL ℝ y)

theorem coefficient_eq_chart (x y : D.domain.boundary.Point)
    (hy : y ∈ (chartAt (Model (d - 1)) x).source) :
    coefficient D x y =
      (ContinuousAlternatingMap.ofSubsingletonLIE
        (𝕜 := ℝ) (E := Model (d - 1)) (F := ℝ) (0 : Fin 1)).symm
        (D.domain.boundary.formInChart x (boundaryAlpha D)
          (chartAt (Model (d - 1)) x y)) := by
  unfold coefficient ambientChart
  rw [TangentBundle.symmL_trivializationAt hy]
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, range_id, mfderivWithin_univ]
  ext v
  simp only [covector, formInChart]
  change (boundaryAlpha D y) (fun _ ↦
      mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1))
        (chartAt (Model (d - 1)) x).symm (chartAt (Model (d - 1)) x y) v) =
    (boundaryAlpha D ((chartAt (Model (d - 1)) x).symm (chartAt (Model (d - 1)) x y)))
      (fun _ ↦ mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1))
        (chartAt (Model (d - 1)) x).symm (chartAt (Model (d - 1)) x y) v)
  congr 1
  congr 1
  exact ((chartAt (Model (d - 1)) x).left_inv hy).symm

theorem coefficient_smooth (x : D.domain.boundary.Point) :
    ContMDiffOn 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1) →L[ℝ] ℝ) ∞
      (coefficient D x) (ambientChart D x).baseSet := by
  have hα : D.domain.boundary.IsSmoothForm (boundaryAlpha D) :=
    D.domain.boundary.isSmoothForm_pullback_one D.domain.extension
      D.domain.boundaryInclusion.map D.liouville.primitive D.liouville.smooth_primitive
  rw [TangentBundle.trivializationAt_baseSet]
  have h := ((ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := Model (d - 1)) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv).contDiff.comp_contDiffOn (hα x)
  have hc : ContMDiffOn 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 1)) ∞
      (chartAt (Model (d - 1)) x) (chartAt (Model (d - 1)) x).source :=
    contMDiffOn_chart
  exact (h.contMDiffOn.comp hc (chartAt (Model (d - 1)) x).mapsTo).congr
    (fun y hy ↦ coefficient_eq_chart D x y hy)

theorem coefficient_chart_apply (x y : D.domain.boundary.Point)
    (hy : y ∈ (ambientChart D x).baseSet) (v : D.domain.boundary.Tangent y) :
    coefficient D x y ((ambientChart D x).continuousLinearEquivAt ℝ y hy v) =
      covector D y v := by
  change covector D y ((ambientChart D x).symmL ℝ y
    ((ambientChart D x).continuousLinearEquivAt ℝ y hy v)) = _
  rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hy]
  rw [ContinuousLinearEquiv.symm_apply_apply]

def fiberChartEquiv (x y : D.domain.boundary.Point)
    (hy : y ∈ (ambientChart D x).baseSet) :
    Fiber D y ≃L[ℝ] (coefficient D x y).ker :=
  kernelCongr ((ambientChart D x).continuousLinearEquivAt ℝ y hy)
    (covector D y) (coefficient D x y) (coefficient_chart_apply D x y hy)

def transverse (x : D.domain.boundary.Point) : Model (d - 1) :=
  (ambientChart D x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt _ _ x)
    (D.liouville.boundaryForm_exists_eval_ne_zero x).choose

theorem transverse_nonzero (x : D.domain.boundary.Point) :
    coefficient D x x (transverse D x) ≠ 0 := by
  rw [transverse, coefficient_chart_apply]
  exact (D.liouville.boundaryForm_exists_eval_ne_zero x).choose_spec

def modelEquiv (x : D.domain.boundary.Point) :
    (coefficient D x x).ker ≃L[ℝ] Model (d - 2) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [← (fiberChartEquiv D x x (mem_baseSet_trivializationAt _ _ x)).finrank_eq]
    rw [D.liouville.boundary_contactHyperplane_finrank, finrank_euclideanSpace_fin])

def chartDomain (x : D.domain.boundary.Point) : Set D.domain.boundary.Point :=
  (ambientChart D x).baseSet ∩ {y | coefficient D x y (transverse D x) ≠ 0}

theorem chartDomain_open (x : D.domain.boundary.Point) : IsOpen (chartDomain D x) :=
  ((coefficient_smooth D x).clm_apply contMDiffOn_const).continuousOn.isOpen_inter_preimage
    (ambientChart D x).open_baseSet isOpen_compl_singleton

theorem mem_chartDomain (x : D.domain.boundary.Point) : x ∈ chartDomain D x :=
  ⟨mem_baseSet_trivializationAt _ _ x, transverse_nonzero D x⟩

/-- Constant forward projection in the ambient chart. -/
def fixedProjection (x : D.domain.boundary.Point) : Model (d - 1) →L[ℝ] Model (d - 2) :=
  (modelEquiv D x).toContinuousLinearMap.comp
    (kernelProjection (coefficient D x x) (transverse D x) (transverse_nonzero D x))

/-- Inverse kernel-chart coordinates, as an ambient-model-valued linear map.
The inverse denominator is only used on `chartDomain`. -/
def reconstruction (x y : D.domain.boundary.Point) : Model (d - 2) →L[ℝ] Model (d - 1) :=
  (ContinuousLinearMap.id ℝ _ - (coefficient D x y).smulRight
    ((coefficient D x y (transverse D x))⁻¹ • transverse D x)).comp
      ((coefficient D x x).ker.subtypeL.comp (modelEquiv D x).symm.toContinuousLinearMap)

theorem reconstruction_smooth (x : D.domain.boundary.Point) :
    ContMDiffOn 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 1)) ∞
      (reconstruction D x) (chartDomain D x) := by
  have ha := (coefficient_smooth D x).mono (t := chartDomain D x) (fun _ hy ↦ hy.1)
  have hi := (ha.clm_apply (contMDiffOn_const (c := transverse D x))).inv₀ (fun y hy ↦ hy.2)
  let C := (coefficient D x x).ker.subtypeL.comp (modelEquiv D x).symm.toContinuousLinearMap
  have hr : ContMDiffOn 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 1)) ∞
      (fun y ↦ C - (coefficient D x y (transverse D x))⁻¹ •
        ((ContinuousLinearMap.toSpanSingleton ℝ (transverse D x)).comp
          ((coefficient D x y).comp C))) (chartDomain D x) :=
    contMDiffOn_const.sub (hi.smul (contMDiffOn_const.clm_comp (ha.clm_comp contMDiffOn_const)))
  apply hr.congr
  intro y hy
  ext v : 1
  simp [reconstruction, C, smul_smul, mul_comm]

def coordinate (x y : D.domain.boundary.Point) : Fiber D y →L[ℝ] Model (d - 2) :=
  (fixedProjection D x).comp
    (((ambientChart D x).continuousLinearMapAt ℝ y).comp
      (D.domain.boundary.contactHyperplane (boundaryAlpha D) y).subtypeL)

def coordinateEquiv (x y : D.domain.boundary.Point) (hy : y ∈ chartDomain D x) :
    Fiber D y ≃L[ℝ] Model (d - 2) :=
  ((fiberChartEquiv D x y hy.1).trans
    (kernelEquiv (coefficient D x y) (coefficient D x x) (transverse D x)
      hy.2 (transverse_nonzero D x))).trans (modelEquiv D x)

theorem coordinateEquiv_apply (x y : D.domain.boundary.Point)
    (hy : y ∈ chartDomain D x) (v : Fiber D y) :
    coordinateEquiv D x y hy v = coordinate D x y v := by
  change modelEquiv D x
    (kernelProjection (coefficient D x x) (transverse D x) (transverse_nonzero D x)
      ((ambientChart D x).continuousLinearEquivAt ℝ y hy.1 v)) = _
  rw [Trivialization.coe_continuousLinearEquivAt_eq]
  rfl

theorem coordinateEquiv_symm_ambient (x y : D.domain.boundary.Point)
    (hy : y ∈ chartDomain D x) (v : Model (d - 2)) :
    ((coordinateEquiv D x y hy).symm v : D.domain.boundary.Tangent y) =
      (ambientChart D x).symmL ℝ y (reconstruction D x y v) := by
  change ((ambientChart D x).continuousLinearEquivAt ℝ y hy.1).symm
    (kernelProjection (coefficient D x y) (transverse D x) hy.2
      ((modelEquiv D x).symm v) : Model (d - 1)) = _
  rw [Trivialization.symm_continuousLinearEquivAt_eq]
  rfl

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Atlas
