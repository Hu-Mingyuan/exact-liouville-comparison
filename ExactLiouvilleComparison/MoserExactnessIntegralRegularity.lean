import ExactLiouvilleComparison.MoserExactnessIntegralStatement
import FsFltz.Geometry.FormScalarDerivative

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set MeasureTheory Filter
namespace ExactLiouvilleComparison.MoserExactnessIntegral
variable {d : ℕ} {M : SmoothManifold d}

/-- Local scalar chart smoothness transports through the actual native chart. -/
theorem contMDiffAt_of_chart {f : M.Point → ℝ} (a x : M.Point)
    (hx : x ∈ (chartAt (Model d) a).source)
    (hf : ContDiffAt ℝ ∞ (f ∘ (chartAt (Model d) a).symm)
      (chartAt (Model d) a x)) :
    ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f x := by
  let c := chartAt (Model d) a
  have hc : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c x :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
      (c.open_source.mem_nhds hx)
  apply (hf.contMDiffAt.comp x hc).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  exact congrArg f (c.left_inv hy).symm

/-- The extension is smooth in space at each required parameter. -/
theorem extension_slice_smooth {f : ℝ → M.Point → ℝ}
    (hf : M.IsSmoothScalarFamily f) (t : ℝ) (ht : t ∈ parameterInterval) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (f t) := by
  intro x
  obtain ⟨U, hU, hsub, hF⟩ := hf x
  have hx := (chartAt (Model d) x).map_source (mem_chart_source (Model d) x)
  apply contMDiffAt_of_chart x x (mem_chart_source _ _)
  exact (hF.contDiffAt (hU.mem_nhds (hsub ⟨ht, hx⟩))).comp _
    (contDiffAt_const.prodMk contDiffAt_id)

/-- In particular every original interval slice is genuinely smooth. -/
theorem slice_smooth {f : Parameter → M.Point → ℝ}
    (hf : M.IsSmoothIntervalScalarFamily f) (t : Parameter) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (f t) := by
  obtain ⟨F, hF, heq⟩ := hf
  rw [← heq t]
  exact extension_slice_smooth hF t t.property

/-- The guard agrees with every genuine extension on the closed interval. -/
theorem integrand_eq_extension {f : Parameter → M.Point → ℝ}
    {F : ℝ → M.Point → ℝ} (hF : ∀ t : Parameter, F t.val = f t)
    {t : ℝ} (ht : t ∈ parameterInterval) (x : M.Point) :
    integrand f t x = F t x := by
  classical
  simp only [integrand, dite_eq_left ht]
  exact congrFun (hF ⟨t, ht⟩).symm x

/-- The literal interval integral is independent of outside values. -/
theorem integral_eq_extension {f : Parameter → M.Point → ℝ}
    {F : ℝ → M.Point → ℝ} (hF : ∀ t : Parameter, F t.val = f t) (x : M.Point) :
    integral f x = ∫ t in (0 : ℝ)..1, F t x := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact integrand_eq_extension hF (by simpa [parameterInterval] using ht) x

/-- Time continuity follows by restricting the genuine smooth chart extension. -/
theorem extension_continuousOn {f : ℝ → M.Point → ℝ}
    (hf : M.IsSmoothScalarFamily f) (x : M.Point) :
    ContinuousOn (fun t => f t x) parameterInterval := by
  let c := chartAt (Model d) x
  obtain ⟨U, hU, hsub, hF⟩ := hf x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source _ _)
  have h : ContinuousOn (fun t => f t (c.symm (c x))) parameterInterval :=
    hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => hsub ⟨ht, hx⟩)
  simpa only [c.left_inv (mem_chart_source _ _)] using h

theorem integrand_continuousOn {f : Parameter → M.Point → ℝ}
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) :
    ContinuousOn (fun t => integrand f t x) parameterInterval := by
  obtain ⟨F, hF, heq⟩ := hf
  exact (extension_continuousOn hF x).congr (fun t ht => integrand_eq_extension heq ht x)

theorem integrand_intervalIntegrable {f : Parameter → M.Point → ℝ}
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) :
    IntervalIntegrable (fun t => integrand f t x) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa [parameterInterval] using integrand_continuousOn hf x

/-- Spatial differentiation on an open joint neighborhood preserves smoothness. -/
theorem spatial_fderiv_smooth {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × E → F} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fun y => g (p.1, y)) p.2) U := by
  have h : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ g p).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) U :=
    (hg.fderiv_of_isOpen hU (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))
  apply h.congr
  intro p hp
  have hi : HasFDerivAt (fun y : E => (p.1, y))
      (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  exact ((hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp
    p.2 hi |>.fderiv

/-- Native scalar derivatives along any fixed tangent vector are continuous in time. -/
theorem extension_derivative_continuousOn {f : ℝ → M.Point → ℝ}
    (hf : M.IsSmoothScalarFamily f) (x : M.Point) (v : M.Tangent x) :
    ContinuousOn (fun t => M.scalarDerivative (f t) x v) parameterInterval := by
  let c := chartAt (Model d) x
  obtain ⟨U, hU, hsub, hF⟩ := hf x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source _ _)
  have hD := spatial_fderiv_smooth hU hF
  have hc : ContinuousOn (fun t =>
      (fderiv ℝ (fun y => f t (c.symm y)) (c x)) (M.chartTangentMap x x v))
      parameterInterval :=
    (hD.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => hsub ⟨ht, hx⟩)).clm_apply continuousOn_const
  apply hc.congr
  intro t ht
  exact (M.fderiv_scalar_in_chart (f t) (extension_slice_smooth hf t ht)
    x x (mem_chart_source _ _) v).symm

theorem derivativeIntegrand_eq_extension {f : Parameter → M.Point → ℝ}
    {F : ℝ → M.Point → ℝ} (hF : ∀ t : Parameter, F t.val = f t)
    {t : ℝ} (ht : t ∈ parameterInterval) (x : M.Point) (v : M.Tangent x) :
    derivativeIntegrand f x v t = M.scalarDerivative (F t) x v := by
  classical
  simp only [derivativeIntegrand, dite_eq_left ht, ← hF ⟨t, ht⟩]

theorem derivativeIntegrand_continuousOn {f : Parameter → M.Point → ℝ}
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) (v : M.Tangent x) :
    ContinuousOn (derivativeIntegrand f x v) parameterInterval := by
  obtain ⟨F, hF, heq⟩ := hf
  exact (extension_derivative_continuousOn hF x v).congr
    (fun t ht => derivativeIntegrand_eq_extension heq ht x v)

theorem derivativeIntegrand_intervalIntegrable {f : Parameter → M.Point → ℝ}
    (hf : M.IsSmoothIntervalScalarFamily f) (x : M.Point) (v : M.Tangent x) :
    IntervalIntegrable (derivativeIntegrand f x v) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa [parameterInterval] using derivativeIntegrand_continuousOn hf x v

/-- Coordinate smoothness on every native chart implies global native smoothness. -/
theorem contMDiff_of_charts {f : M.Point → ℝ}
    (hf : ∀ a, ContDiffOn ℝ ∞ (f ∘ (chartAt (Model d) a).symm)
      (chartAt (Model d) a).target) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f := by
  intro x
  exact contMDiffAt_of_chart x x (mem_chart_source _ _)
    ((hf x).contDiffAt ((chartAt (Model d) x).open_target.mem_nhds
      ((chartAt (Model d) x).map_source (mem_chart_source _ _))))

/-- Equality of the complete coordinate integral functions, without endpoint
smoothness claims for the guard. -/
theorem integral_comp_inverseChart {f : Parameter → M.Point → ℝ}
    {F : ℝ → M.Point → ℝ} (heq : ∀ t : Parameter, F t.val = f t) (a : M.Point) :
    integral f ∘ (chartAt (Model d) a).symm =
      fun y => ∫ t in (0 : ℝ)..1, F t ((chartAt (Model d) a).symm y) := by
  funext y
  exact integral_eq_extension heq _

/-- Operator-valued spatial derivatives are continuous on compact time. -/
theorem extension_chart_derivative_continuousOn {f : ℝ → M.Point → ℝ}
    (hf : M.IsSmoothScalarFamily f) (a : M.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target) :
    ContinuousOn (fun t => fderiv ℝ (fun z => f t ((chartAt (Model d) a).symm z)) y)
      parameterInterval := by
  obtain ⟨U, hU, hsub, hF⟩ := hf a
  exact (spatial_fderiv_smooth hU hF).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun t ht => hsub ⟨ht, hy⟩)

theorem extension_chart_derivative_intervalIntegrable {f : ℝ → M.Point → ℝ}
    (hf : M.IsSmoothScalarFamily f) (a : M.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target) :
    IntervalIntegrable
      (fun t => fderiv ℝ (fun z => f t ((chartAt (Model d) a).symm z)) y) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa [parameterInterval] using extension_chart_derivative_continuousOn hf a y hy

set_option backward.isDefEq.respectTransparency false in
/-- The integral of the guarded native derivative is the chart derivative
integral applied to the actual chart transport of the tangent vector. -/
theorem derivativeIntegral_eq_chart {f : Parameter → M.Point → ℝ}
    {F : ℝ → M.Point → ℝ} (hF : M.IsSmoothScalarFamily F)
    (heq : ∀ t : Parameter, F t.val = f t) (x : M.Point) (v : M.Tangent x) :
    (∫ t in (0 : ℝ)..1, derivativeIntegrand f x v t) =
      (∫ t in (0 : ℝ)..1,
        fderiv ℝ (fun y => F t ((chartAt (Model d) x).symm y)) (chartAt (Model d) x x))
        (M.chartTangentMap x x v) := by
  rw [ContinuousLinearMap.intervalIntegral_apply
    (extension_chart_derivative_intervalIntegrable hF x _
      ((chartAt (Model d) x).map_source (mem_chart_source _ _)))]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ parameterInterval := by simpa [parameterInterval] using ht
  rw [derivativeIntegrand_eq_extension heq ht']
  exact (M.fderiv_scalar_in_chart (F t) (extension_slice_smooth hF t ht')
    x x (mem_chart_source _ _) v).symm

end ExactLiouvilleComparison.MoserExactnessIntegral
