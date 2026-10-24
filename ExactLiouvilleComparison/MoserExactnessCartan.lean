import ExactLiouvilleComparison.MoserExactnessCartanCharts
import ExactLiouvilleComparison.MoserExactnessCartanCalculus

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

/-- Evaluation of an intrinsic covector in any chart containing the base point. -/
theorem evalOne_chart (alpha : M.Form 1) (a x : M.Point)
    (hx : x ∈ (chartAt (Model d) a).source) (v : M.Tangent x) :
    M.formInChart a alpha (chartAt (Model d) a x)
      (fun _ => M.chartTangentMap a x v) = evalOne alpha x v :=
  congrArg (fun beta => beta (fun _ : Fin 1 => v))
    (M.formInChart_comp_chartTangentMap alpha a x hx)

set_option backward.isDefEq.respectTransparency false in
/-- Pullback evaluation agrees with the spatial part of its joint chart expression. -/
theorem chart_pullback_eval (f : ℝ → M.Point → M.Point)
    (hf : M.IsSmoothMapFamily M f) (t : Parameter) (alpha : M.Form 1)
    (a b x : M.Point) (hx : x ∈ (chartAt (Model d) a).source)
    (hb : f t.val x ∈ (chartAt (Model d) b).source) (v : M.Tangent x) :
    evalOne (M.pullback M (f t.val) alpha) x v =
      M.formInChart b alpha (chartAt (Model d) b (f t.val x))
        (fun _ => fderiv ℝ (fun p : ℝ × Model d =>
          chartAt (Model d) b (f p.1 ((chartAt (Model d) a).symm p.2)))
          (t.val, chartAt (Model d) a x) (0, M.chartTangentMap a x v)) := by
  let c := chartAt (Model d) a
  have hsp := chart_mapFamily_spatial f hf t a b (c x)
    (M.chartTangentMap a x v) (c.map_source hx) (by rwa [c.left_inv hx])
  have hinv := congrArg (fun L => L v)
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx)
  change M.inverseChartTangentMap a (c x) (M.chartTangentMap a x v) = v at hinv
  rw [hinv, c.left_inv hx] at hsp
  rw [hsp, evalOne_chart alpha b (f t.val x) hb]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The time coefficient in a source chart is the literal pulled-back contraction. -/
theorem chart_contraction_eval (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x} (E : FirstPathFlow.Evolution Z)
    (t : Parameter) (a b : M.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target)
    (hb : E.map parameterZero t ((chartAt (Model d) a).symm y) ∈
      (chartAt (Model d) b).source) :
    M.formInChart b (mu t.val)
      (chartAt (Model d) b (E.extension 0 t.val ((chartAt (Model d) a).symm y)))
      (fun _ => fderiv ℝ (fun p : ℝ × Model d =>
        chartAt (Model d) b (E.extension 0 p.1 ((chartAt (Model d) a).symm p.2)))
        (t.val, y) (1, 0)) = contractionAlong mu E t ((chartAt (Model d) a).symm y) := by
  have ht := chart_evolution_time E parameterZero t a b y hy hb
  change fderiv ℝ (fun p : ℝ × Model d =>
    chartAt (Model d) b (E.extension 0 p.1 ((chartAt (Model d) a).symm p.2)))
    (t.val, y) (1, 0) = _ at ht
  rw [ht]
  change M.formInChart b (mu t.val)
    (chartAt (Model d) b (E.extension parameterZero.val t.val ((chartAt (Model d) a).symm y))) _ = _
  rw [E.agrees parameterZero t]
  exact evalOne_chart _ _ _ hb _

set_option backward.isDefEq.respectTransparency false in
/-- Full time-dependent Cartan pullback calculus on the accepted native manifold,
including within derivatives at the two endpoints. -/
theorem cartanTarget : CartanTarget (M := M) := by
  intro mu hmu Z hZ E t x v
  let f := E.extension 0
  have hf : M.IsSmoothMapFamily M f := evolution_isSmoothMapFamily E parameterZero
  let Y := E.map parameterZero t x
  let c := chartAt (Model d) x
  let b := chartAt (Model d) Y
  let y := c x
  let V := M.chartTangentMap x x v
  let w := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (E.map parameterZero t) x v
  let g := fun p : ℝ × Model d => b (f p.1 (c.symm p.2))
  let A := fun p : ℝ × Model d => M.formInChart Y (mu p.1) p.2
  have hx : x ∈ c.source := mem_chart_source _ _
  have hy : y ∈ c.target := c.map_source hx
  have hbx : Y ∈ b.source := mem_chart_source _ _
  have hfx : f t.val x = Y := congrFun (E.agrees parameterZero t) x
  have hfg : f t.val (c.symm y) = Y := by rw [c.left_inv hx]; exact hfx
  have hg : ContDiffAt ℝ ∞ g (t.val, y) :=
    contDiffAt_chart_mapFamily f hf t x Y y hy (by rw [hfg]; exact hbx)
  have hgy : g (t.val, y) = b Y := congrArg b hfg
  obtain ⟨U, hU, hUc, hAU⟩ := hmu Y
  have hA : ContDiffAt ℝ ∞ A (t.val, g (t.val, y)) := by
    rw [hgy]
    exact hAU.contDiffAt (hU.mem_nhds (hUc ⟨t.property, b.map_source hbx⟩))
  have hcoord := coordinate_cartan_forms A g t.val y V hA hg
  have htime : fderiv ℝ g (t.val, y) (1, 0) = M.chartTangentMap Y Y (Z t Y) := by
    have h := chart_evolution_time E parameterZero t x Y y hy (by rw [c.left_inv hx]; exact hbx)
    change fderiv ℝ g (t.val, y) (1, 0) =
      M.chartTangentMap Y (E.map parameterZero t (c.symm y))
        (Z t (E.map parameterZero t (c.symm y))) at h
    rw [c.left_inv hx] at h
    exact h
  have hspace : fderiv ℝ g (t.val, y) (0, V) = M.chartTangentMap Y Y w := by
    have h := chart_mapFamily_spatial f hf t x Y y V hy (by rw [hfg]; exact hbx)
    have hinv := congrArg (fun L => L v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm_comp_deriv hx)
    change M.inverseChartTangentMap x y V = v at hinv
    rw [hinv, c.left_inv hx] at h
    change fderiv ℝ g (t.val, y) (0, V) = _ at h
    have hag : f t.val = E.map parameterZero t := E.agrees parameterZero t
    rw [hag] at h
    exact h
  have htform : deriv (fun u => A (u, g (t.val, y))
      (fun _ => fderiv ℝ g (t.val, y) (0, V))) t.val =
      deriv (fun u => evalOne (mu u) Y w) t.val := by
    rw [hgy, hspace]
    congr 1
    funext u
    exact evalOne_chart (mu u) Y Y hbx w
  have hext : extDeriv (fun z => A (t.val, z)) (g (t.val, y))
      ![fderiv ℝ g (t.val, y) (1, 0), fderiv ℝ g (t.val, y) (0, V)] =
      evalTwo (M.exteriorDerivative (mu t.val)) Y (Z t Y) w := by
    rw [hgy, htime, hspace]
    change _ = extDeriv (M.formInChart Y (mu t.val)) (b Y)
      (fun i => M.chartTangentMap Y Y (![Z t Y, w] i))
    congr 1
    funext i
    fin_cases i <;> rfl
  have hlocal : (fun z => A (t.val, g (t.val, z))
      (fun _ => fderiv ℝ g (t.val, z) (1, 0))) =ᶠ[𝓝 y]
      contractionAlong mu E t ∘ c.symm := by
    have hcont := ((E.map parameterZero t).contMDiff.continuous.continuousAt.comp
      (c.continuousAt_symm hy))
    have hbnear : ∀ᶠ z in 𝓝 y, E.map parameterZero t (c.symm z) ∈ b.source :=
      hcont.preimage_mem_nhds (b.open_source.mem_nhds (by change E.map parameterZero t (c.symm y) ∈ b.source; rw [c.left_inv hx]; exact hbx))
    filter_upwards [c.open_target.mem_nhds hy, hbnear] with z hz hzb
    exact chart_contraction_eval mu E t x Y z hz hzb
  have hscalar : ContDiffAt ℝ ∞ (contractionAlong mu E t ∘ c.symm) y := by
    obtain ⟨q, hq, hqt⟩ := contractionAlong_isSmoothIntervalScalarFamily mu hmu hZ E
    obtain ⟨W, hW, hWc, hqW⟩ := hq x
    have h := (hqW.contDiffAt (hW.mem_nhds (hWc (show (t.val, y) ∈ parameterInterval ×ˢ c.target from ⟨t.property, hy⟩)))).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
    change ContDiffAt ℝ ∞ (fun z => q t.val (c.symm z)) y at h
    rw [hqt t] at h
    exact h
  have hscalarDeriv : fderiv ℝ (fun z => A (t.val, g (t.val, z))
      (fun _ => fderiv ℝ g (t.val, z) (1, 0))) y V =
      M.scalarDerivative (contractionAlong mu E t) x v := by
    rw [hlocal.fderiv_eq]
    exact (scalarDerivative_eq_chart _ x x hx hscalar v).symm
  rw [htform, hext, hscalarDeriv] at hcoord
  apply hcoord.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ t.property
  have hnative : ContinuousAt (fun u => f u x) t.val := by
    obtain ⟨R, hR, hRc, hfR⟩ := hf
    exact ((hfR.contMDiffAt (hR.mem_nhds
      (hRc (show (t.val, x) ∈ parameterInterval ×ˢ univ from ⟨t.property, mem_univ _⟩)))).comp t.val
        (contMDiffAt_id.prodMk contMDiffAt_const)).continuousAt
  have hbnear : ∀ᶠ u in 𝓝 t.val, f u x ∈ b.source :=
    hnative.preimage_mem_nhds (b.open_source.mem_nhds (by rw [hfx]; exact hbx))
  filter_upwards [self_mem_nhdsWithin, hbnear.filter_mono nhdsWithin_le_nhds] with u hu hub
  have h := chart_pullback_eval f hf ⟨u, hu⟩ (mu u) x Y x hx hub v
  change evalOne (M.pullback M (f u) (mu u)) x v = _
  change evalOne (M.pullback M (f u) (mu u)) x v =
    M.formInChart Y (mu u) (b (f u (c.symm y)))
      (fun _ => fderiv ℝ g (u, y) (0, V))
  rw [c.left_inv hx]
  exact h
end ExactLiouvilleComparison.MoserExactness
