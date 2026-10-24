import ExactLiouvilleComparison.SteinReferenceAmbient

/-! Pullback to an arbitrary native manifold from a normed vector space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.SteinReferenceConstruction

variable {d : ℕ} (M : SmoothManifold d)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pullback by the actual native real derivative. -/
def pullbackAmbient {k : ℕ} (f : M.Point → E) (eta : E → E [⋀^Fin k]→L[ℝ] ℝ) : M.Form k :=
  fun x => (eta (f x)).compContinuousLinearMap
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f x)

theorem pullbackAmbient_in_chart {k : ℕ} (f : M.Point → E)
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) ∞ f)
    (eta : E → E [⋀^Fin k]→L[ℝ] ℝ) (a : M.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target) :
    M.formInChart a (pullbackAmbient M f eta) y =
      (eta ((f ∘ (chartAt (Model d) a).symm) y)).compContinuousLinearMap
        (fderiv ℝ (f ∘ (chartAt (Model d) a).symm) y) := by
  rw [← M.mfderiv_comp_inverseChart (hf.mdifferentiable (by simp)) a hy]
  ext vs
  rfl

theorem exteriorDerivative_pullbackAmbient {k : ℕ} (f : M.Point → E)
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) ∞ f)
    (eta : E → E [⋀^Fin k]→L[ℝ] ℝ) (heta : Differentiable ℝ eta) :
    M.exteriorDerivative (pullbackAmbient M f eta) =
      pullbackAmbient M f (extDeriv eta) := by
  funext x
  let c := chartAt (Model d) x
  have hx : x ∈ c.source := mem_chart_source _ _
  have hy : c x ∈ c.target := c.map_source hx
  have he : M.formInChart x (pullbackAmbient M f eta) =ᶠ[nhds (c x)]
      fun y => (eta ((f ∘ c.symm) y)).compContinuousLinearMap
        (fderiv ℝ (f ∘ c.symm) y) := by
    filter_upwards [c.open_target.mem_nhds hy] with y hy
    exact pullbackAmbient_in_chart M f hf eta x y hy
  have hc := (M.contDiffOn_comp_inverseChart hf x).contDiffAt
    (c.open_target.mem_nhds hy)
  change (extDeriv (M.formInChart x (pullbackAmbient M f eta)) (c x)).compContinuousLinearMap
    (M.chartTangentMap x x) = _
  rw [he.extDeriv_eq, extDeriv_pullback (heta _) hc (by simp)]
  rw [← M.mfderiv_comp_inverseChart (hf.mdifferentiable (by simp)) x hy]
  have hcx : (chartAt (Model d) x).symm (c x) = x := c.left_inv hx
  simp only [Function.comp_apply, hcx]
  have hd : (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f
      ((chartAt (Model d) x).symm (c x)) : Model d →L[ℝ] E) =
      mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f x :=
    by rw [hcx]
  rw [hd]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm_comp_deriv hx
  ext vs
  change extDeriv eta (f x) (fun j =>
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f x)
      ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c.symm (c x))
        ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c x) (vs j)))) = _
  apply congrArg (extDeriv eta (f x))
  funext j
  exact congrArg (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f x)
    (congrArg (fun L => L (vs j)) hinv)

/-- A smooth covector family on the ambient space pulls back to a smooth form. -/
theorem smooth_pullbackAmbient_one (f : M.Point → E)
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) ∞ f)
    (b : E → E →L[ℝ] ℝ) (hb : ContDiff ℝ ∞ b) :
    M.IsSmoothForm (pullbackAmbient M f (fun z =>
      ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1) (b z))) := by
  apply isSmoothForm_covectorForm M
    (fun x => (b (f x)).comp (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f x))
  intro a
  have hb' := hb.comp_contDiffOn (M.contDiffOn_comp_inverseChart hf a)
  have hd := M.contDiffOn_mfderiv_comp_inverseChart hf a
  exact (hb'.clm_comp hd).congr (fun y _ => by ext v; rfl)

end ExactLiouvilleComparison.SteinReferenceConstruction
