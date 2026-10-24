import ExactLiouvilleComparison.MoserExactnessStatement

/-! Native scalar zero-forms and the exterior-derivative consequence of exactness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

/-- Restrict genuine jointly smooth coefficients to any time in the closed interval. -/
theorem smoothForm_at {k : ℕ} (mu : ℝ → M.Form k)
    (hmu : M.IsSmoothFormFamily mu) (t : Parameter) : M.IsSmoothForm (mu t.val) := by
  intro a
  obtain ⟨U, _, hcover, hcoeff⟩ := hmu a
  exact hcoeff.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun y hy => hcover ⟨t.property, hy⟩)

/-- The standard identification of real functions with native zero-forms. -/
def scalarForm (h : M.Point → ℝ) : M.Form 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (M.Tangent x) (Fin 0) (h x)

theorem formInChart_scalarForm (h : M.Point → ℝ) (a : M.Point) :
    M.formInChart a (scalarForm h) = fun y =>
      ContinuousAlternatingMap.constOfIsEmpty ℝ (Model d) (Fin 0)
        (h ((chartAt (Model d) a).symm y)) := by
  funext y
  ext vs
  rfl

theorem scalarForm_smooth (h : M.Point → ℝ)
    (hh : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ h) : M.IsSmoothForm (scalarForm h) := by
  intro a
  rw [formInChart_scalarForm]
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Model d) ℝ (Fin 0)).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (M.contDiffOn_comp_inverseChart hh a)

theorem evalOne_exteriorDerivative_scalarForm (h : M.Point → ℝ)
    (hh : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ h) (x : M.Point) (v : M.Tangent x) :
    evalOne (M.exteriorDerivative (scalarForm h)) x v = M.scalarDerivative h x v := by
  unfold evalOne exteriorDerivative
  rw [formInChart_scalarForm, extDeriv_constOfIsEmpty]
  exact M.fderiv_scalar_in_chart h hh x x (mem_chart_source _ _) v

/-- Exact primitive equality implies the exterior-derivative equality, using
native naturality and d²=0. This requires no ODE or metric assumption. -/
theorem exterior_eq_of_primitive_eq (mu₀ mu₁ : M.Form 1)
    (h₀ : M.IsSmoothForm mu₀) (h₁ : M.IsSmoothForm mu₁)
    (F : M.SmoothEquiv M) (h : M.Point → ℝ)
    (hh : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ h)
    (he : ∀ x v, evalOne (M.pullback M F mu₁) x v =
      evalOne mu₀ x v + M.scalarDerivative h x v) :
    M.pullback M F (M.exteriorDerivative mu₁) = M.exteriorDerivative mu₀ := by
  have hform : M.pullback M F mu₁ = mu₀ + M.exteriorDerivative (scalarForm h) := by
    funext x
    ext vs
    have hvs : vs = fun _ => vs 0 := by funext i; fin_cases i; rfl
    rw [hvs]
    exact (he x (vs 0)).trans (by
      rw [← evalOne_exteriorDerivative_scalarForm h hh]
      rfl)
  have hnat := M.exteriorDerivative_pullback M
    (⟨F, F.contMDiff⟩ : M.SmoothMap M) mu₁ h₁
  change M.exteriorDerivative (M.pullback M F mu₁) =
    M.pullback M F (M.exteriorDerivative mu₁) at hnat
  rw [← hnat, hform, RadialInterpolation.exteriorDerivative_add h₀
    (M.isSmoothForm_exteriorDerivative _ (scalarForm_smooth h hh)),
    M.exteriorDerivative_exteriorDerivative _ (scalarForm_smooth h hh), add_zero]

end ExactLiouvilleComparison.MoserExactness
