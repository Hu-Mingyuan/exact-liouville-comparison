import ExactLiouvilleComparison.CylindricalCompatibilityContactReeb
import FsFltz.Geometry.VectorFieldBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {n : ℕ}

private theorem single_eq_const (v : Model n) : ![v] = (fun _ : Fin 1 => v) := by
  ext i
  fin_cases i
  rfl

private theorem pull_one (a : Model n [⋀^Fin 1]→L[ℝ] ℝ)
    (e : Model n →L[ℝ] Model n) (v : Model n) :
    a.compContinuousLinearMap e ![v] = a ![e v] := by
  apply congrArg a
  ext i
  fin_cases i
  rfl

private theorem pull_two (b : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (e : Model n →L[ℝ] Model n) (v w : Model n) :
    b.compContinuousLinearMap e ![v, w] = b ![e v, e w] := by
  apply congrArg b
  ext i
  fin_cases i <;> rfl

private theorem augmented_pull_invertible
    (a : Model n [⋀^Fin 1]→L[ℝ] ℝ) (b : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ∃ w, a ![w] ≠ 0)
    (hb : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → b ![v, w] = 0) → v = 0)
    (e : Model n ≃L[ℝ] Model n) :
    (augmentedContactOperator (a.compContinuousLinearMap e.toContinuousLinearMap)
      (b.compContinuousLinearMap e.toContinuousLinearMap)).IsInvertible := by
  apply augmentedContactOperator_invertible
  · obtain ⟨w, hw⟩ := ha
    refine ⟨e.symm w, ?_⟩
    simpa only [pull_one, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] using hw
  · intro v hv hh
    apply e.injective
    rw [map_zero]
    apply hb
    · exact (pull_one a e.toContinuousLinearMap v) ▸ hv
    · intro w hw
      have hk : a.compContinuousLinearMap e.toContinuousLinearMap ![e.symm w] = 0 := by
        simpa only [pull_one, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] using hw
      simpa only [pull_two, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] using hh (e.symm w) hk

private theorem augmented_apply_of_reeb
    (a : Model n [⋀^Fin 1]→L[ℝ] ℝ) (b : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (v : Model n) (hn : a ![v] = 1) (hk : ∀ w, b ![v, w] = 0) :
    augmentedContactOperator a b (v, 0) = (0, 1) := by
  apply Prod.ext
  · apply (chartOneFormEquiv n).injective
    rw [augmentedContactOperator_fst]
    simp only [zero_smul, add_zero, map_zero]
    ext vs
    have hvs : vs = ![vs 0] := by ext i; fin_cases i; rfl
    rw [hvs]
    exact hk _
  · exact (augmentedContactOperator_snd a b (v, 0)).trans hn

/-- Smoothness of augmented inversion coefficients is proved in finite-dimensional
native continuous-linear-map spaces, with both input forms varying. -/
private theorem augmented_contDiff : ContDiff ℝ ∞
    (fun p : (Model n [⋀^Fin 1]→L[ℝ] ℝ) × (Model n [⋀^Fin 2]→L[ℝ] ℝ) =>
      augmentedContactOperator p.1 p.2) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model n [⋀^Fin 2]→L[ℝ] ℝ) → Model n →L[ℝ] Model n [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model n [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model n →L[ℝ] Model n [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model n) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hc : ContDiff ℝ ∞ (fun p : (Model n [⋀^Fin 1]→L[ℝ] ℝ) ×
      (Model n [⋀^Fin 2]→L[ℝ] ℝ) => p.2.curryLeft v.1) :=
    (hcur.comp contDiff_snd).clm_apply contDiff_const
  have ha : ContDiff ℝ ∞ (fun p : (Model n [⋀^Fin 1]→L[ℝ] ℝ) ×
      (Model n [⋀^Fin 2]→L[ℝ] ℝ) => (chartOneFormEquiv n).symm p.1) :=
    (chartOneFormEquiv n).symm.contDiff.comp contDiff_fst
  have hb := (chartOneFormEquiv n).symm.contDiff.comp hc
  have he : ContDiff ℝ ∞ (fun p : (Model n [⋀^Fin 1]→L[ℝ] ℝ) ×
      (Model n [⋀^Fin 2]→L[ℝ] ℝ) =>
      ((ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)).symm p.1) v.1) :=
    ((ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := Model n) (F := ℝ) (0 : Fin 1)).symm.contDiff.comp
        contDiff_fst).clm_apply contDiff_const
  exact (hb.add (ha.const_smul v.2)).prodMk he

private theorem augmented_inverse_smoothOn
    (a : Model n → Model n [⋀^Fin 1]→L[ℝ] ℝ)
    (b : Model n → Model n [⋀^Fin 2]→L[ℝ] ℝ) (s : Set (Model n))
    (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s)
    (hi : ∀ y ∈ s, (augmentedContactOperator (a y) (b y)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun y => ((augmentedContactOperator (a y) (b y)).inverse (0, 1)).1) s := by
  have hab : ContDiffOn ℝ ∞ (fun y => (a y, b y)) s := ha.prodMk hb
  have hA := (augmented_contDiff (n := n)).comp_contDiffOn hab
  have hAi : ContDiffOn ℝ ∞ (fun y => (augmentedContactOperator (a y) (b y)).inverse) s := by
    intro y hy
    exact (hi y hy).contDiffAt_map_inverse.comp_contDiffWithinAt y (hA y hy)
  exact (hAi.clm_apply (contDiffOn_const (c := ((0 : Model n), (1 : ℝ))))).fst

variable {d : ℕ}

private def inverseChartEquiv (M : SmoothManifold d) (a : M.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target) : Model d ≃L[ℝ] Model d := by
  let x := (chartAt (Model d) a).symm y
  have hx := (chartAt (Model d) a).map_target hy
  have hxy := (chartAt (Model d) a).right_inv hy
  refine ContinuousLinearEquiv.equivOfInverse (M.inverseChartTangentMap a y)
    (M.chartTangentMap a x) ?_ ?_
  · intro v
    have h := congrArg (fun L => L v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).comp_symm_deriv hy)
    exact h
  · intro v
    have h := congrArg (fun L => L v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx)
    change M.inverseChartTangentMap a (chartAt (Model d) a x)
      (M.chartTangentMap a x v) = v at h
    erw [hxy] at h
    exact h

private theorem boundary_chart_augmented_invertible (D : LiouvilleDomain d)
    (a : D.domain.boundary.Point) (y : Model (d - 1))
    (hy : y ∈ (chartAt (Model (d - 1)) a).target) :
    (augmentedContactOperator (D.domain.boundary.formInChart a (alpha D) y)
      (D.domain.boundary.formInChart a (D.domain.boundary.exteriorDerivative (alpha D)) y)).IsInvertible := by
  let M := D.domain.boundary
  let x := (chartAt (Model (d - 1)) a).symm y
  apply augmented_pull_invertible (alpha D x) (M.exteriorDerivative (alpha D) x)
    ?_ ?_ (inverseChartEquiv M a y hy)
  · obtain ⟨v, hv⟩ := D.liouville.boundaryForm_exists_eval_ne_zero x
    refine ⟨v, ?_⟩
    rw [single_eq_const]
    exact hv
  · intro v hv hh
    apply D.liouville.boundaryForm_differential_nondegenerate_on_kernel x v
    · rw [single_eq_const] at hv
      exact hv
    · intro w hw
      apply hh w
      rw [single_eq_const]
      exact hw

private theorem boundaryReeb_chart_eq (D : LiouvilleDomain d)
    (a : D.domain.boundary.Point) (y : Model (d - 1))
    (hy : y ∈ (chartAt (Model (d - 1)) a).target) :
    D.domain.boundary.vectorInChart a (boundaryReeb D) y =
      ((augmentedContactOperator (D.domain.boundary.formInChart a (alpha D) y)
        (D.domain.boundary.formInChart a (D.domain.boundary.exteriorDerivative (alpha D)) y)).inverse
          (0, 1)).1 := by
  let M := D.domain.boundary
  let x := (chartAt (Model (d - 1)) a).symm y
  let e := inverseChartEquiv M a y hy
  let V := M.vectorInChart a (boundaryReeb D) y
  have hV : e V = boundaryReeb D x := e.apply_symm_apply _
  have hn : M.formInChart a (alpha D) y ![V] = 1 := by
    change (alpha D x).compContinuousLinearMap e.toContinuousLinearMap ![V] = 1
    erw [pull_one, hV]
    rw [single_eq_const]
    exact boundaryReeb_normalized D x
  have hk (w : Model (d - 1)) :
      M.formInChart a (M.exteriorDerivative (alpha D)) y ![V, w] = 0 := by
    change (M.exteriorDerivative (alpha D) x).compContinuousLinearMap e.toContinuousLinearMap ![V, w] = 0
    erw [pull_two, hV]
    exact boundaryReeb_kernel D x (e w)
  have he := augmented_apply_of_reeb _ _ V hn hk
  have hi := boundary_chart_augmented_invertible D a y hy
  have h := congrArg (fun z => (augmentedContactOperator
    (M.formInChart a (alpha D) y)
    (M.formInChart a (M.exteriorDerivative (alpha D)) y)).inverse z) he
  rw [hi.inverse_apply_self] at h
  exact congrArg Prod.fst h

/-- The actual normalized boundary Reeb field is smooth in every native chart. -/
theorem boundaryReeb_smooth (D : LiouvilleDomain d) :
    D.domain.boundary.IsSmoothVectorField (boundaryReeb D) := by
  have ha : D.domain.boundary.IsSmoothForm (alpha D) :=
    D.domain.boundary.isSmoothForm_pullback_one D.domain.extension D.domain.boundaryInclusion.map
      D.liouville.primitive D.liouville.smooth_primitive
  have hb := D.domain.boundary.isSmoothForm_exteriorDerivative (alpha D) ha
  intro a
  apply (augmented_inverse_smoothOn
    (D.domain.boundary.formInChart a (alpha D))
    (D.domain.boundary.formInChart a (D.domain.boundary.exteriorDerivative (alpha D)))
    (chartAt (Model (d - 1)) a).target (ha a) (hb a)
    (boundary_chart_augmented_invertible D a)).congr
  intro y hy
  exact boundaryReeb_chart_eq D a y hy

/-- The first four fields of contact data are constructed without a compatible J. -/
theorem reebExistenceTarget : ReebExistenceTarget := by
  intro d D
  exact ⟨boundaryReeb D, boundaryReeb_smooth D, boundaryReeb_normalized D, boundaryReeb_kernel D⟩

end ExactLiouvilleComparison.CylindricalCompatibility
