import ExactLiouvilleComparison.MoserExactnessCartanRegularity

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

set_option backward.isDefEq.respectTransparency false in
/-- Native joint smoothness becomes ordinary joint smoothness in two fixed charts. -/
theorem contDiffAt_chart_mapFamily (f : ℝ → M.Point → M.Point)
    (hf : M.IsSmoothMapFamily M f) (t : Parameter) (a b : M.Point)
    (y : Model d) (hy : y ∈ (chartAt (Model d) a).target)
    (hb : f t.val ((chartAt (Model d) a).symm y) ∈ (chartAt (Model d) b).source) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Model d =>
      chartAt (Model d) b (f p.1 ((chartAt (Model d) a).symm p.2))) (t.val, y) := by
  obtain ⟨U, hU, hUc, hfU⟩ := hf
  have hci := (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
    ((chartAt (Model d) a).open_target.mem_nhds hy)
  have hq : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × Model d => (p.1, (chartAt (Model d) a).symm p.2)) (t.val, y) :=
    contMDiffAt_fst.prodMk (hci.comp _ contMDiffAt_snd)
  have hF := (hfU.contMDiffAt (hU.mem_nhds (hUc (show (t.val, (chartAt (Model d) a).symm y) ∈ parameterInterval ×ˢ univ from ⟨t.property, mem_univ _⟩)))).comp
    (t.val, y) hq
  have hcb := (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := b)).contMDiffAt
    ((chartAt (Model d) b).open_source.mem_nhds hb)
  have h := hcb.comp (t.val, y) hF
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffAt

/-- Smoothness of a map family gives native differentiability of each interval slice. -/
theorem mdifferentiableAt_mapFamily (f : ℝ → M.Point → M.Point)
    (hf : M.IsSmoothMapFamily M f) (t : Parameter) (x : M.Point) :
    MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (f t.val) x := by
  obtain ⟨U, hU, hUc, hfU⟩ := hf
  exact ((hfU.contMDiffAt (hU.mem_nhds (hUc (show (t.val, x) ∈ parameterInterval ×ˢ univ from ⟨t.property, mem_univ _⟩)))).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The spatial part of the joint coordinate derivative is the actual transported
native differential, with both chart derivatives present. -/
theorem chart_mapFamily_spatial (f : ℝ → M.Point → M.Point)
    (hf : M.IsSmoothMapFamily M f) (t : Parameter) (a b : M.Point)
    (y v : Model d) (hy : y ∈ (chartAt (Model d) a).target)
    (hb : f t.val ((chartAt (Model d) a).symm y) ∈ (chartAt (Model d) b).source) :
    fderiv ℝ (fun p : ℝ × Model d =>
      chartAt (Model d) b (f p.1 ((chartAt (Model d) a).symm p.2))) (t.val, y) (0, v) =
    M.chartTangentMap b (f t.val ((chartAt (Model d) a).symm y))
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (f t.val)
        ((chartAt (Model d) a).symm y) (M.inverseChartTangentMap a y v)) := by
  let g := fun p : ℝ × Model d =>
    chartAt (Model d) b (f p.1 ((chartAt (Model d) a).symm p.2))
  have hg := (contDiffAt_chart_mapFamily f hf t a b y hy hb).differentiableAt (by simp)
  have hs := (hg.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t.val y)).fderiv
  have hs' := congrArg (fun L => L v) hs
  change fderiv ℝ (fun z => g (t.val, z)) y v = fderiv ℝ g (t.val, y) (0, v) at hs'
  rw [← hs']
  change fderiv ℝ (chartAt (Model d) b ∘ f t.val ∘ (chartAt (Model d) a).symm) y v = _
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp y ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) b).mdifferentiableAt hb)
      ((mdifferentiableAt_mapFamily f hf t _).comp y
        ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy)),
    mfderiv_comp y (mdifferentiableAt_mapFamily f hf t _)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The joint coordinate derivative in time is the actual evolution field.
Uniqueness of within derivatives on Icc proves this at both endpoints as well. -/
theorem chart_evolution_time {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) (s t : Parameter) (a b : M.Point)
    (y : Model d) (hy : y ∈ (chartAt (Model d) a).target)
    (hb : E.map s t ((chartAt (Model d) a).symm y) ∈ (chartAt (Model d) b).source) :
    fderiv ℝ (fun p : ℝ × Model d =>
      chartAt (Model d) b (E.extension s.val p.1 ((chartAt (Model d) a).symm p.2)))
      (t.val, y) (1, 0) =
    M.chartTangentMap b (E.map s t ((chartAt (Model d) a).symm y))
      (Z t (E.map s t ((chartAt (Model d) a).symm y))) := by
  have hb' : E.extension s.val t.val ((chartAt (Model d) a).symm y) ∈
      (chartAt (Model d) b).source := by rw [E.agrees s t]; exact hb
  have hg := (contDiffAt_chart_mapFamily (E.extension s.val)
    (evolution_isSmoothMapFamily E s) t a b y hy hb').differentiableAt (by simp)
  have hd := hg.hasFDerivAt.comp_hasDerivAt t.val
    ((hasDerivAt_id t.val).prodMk (hasDerivAt_const t.val y))
  have ho := E.chart_solves s t ((chartAt (Model d) a).symm y) b hb
  have hu : UniqueDiffWithinAt ℝ parameterInterval t.val :=
    uniqueDiffOn_Icc_zero_one t.val t.property
  exact (hd.hasDerivWithinAt.derivWithin hu).symm.trans (ho.derivWithin hu)

set_option backward.isDefEq.respectTransparency false in
/-- A smooth scalar coordinate expression computes the actual native derivative. -/
theorem scalarDerivative_eq_chart (f : M.Point → ℝ) (a x : M.Point)
    (hx : x ∈ (chartAt (Model d) a).source)
    (hf : ContDiffAt ℝ ∞ (f ∘ (chartAt (Model d) a).symm) (chartAt (Model d) a x))
    (v : M.Tangent x) :
    M.scalarDerivative f x v =
      fderiv ℝ (f ∘ (chartAt (Model d) a).symm) (chartAt (Model d) a x)
        (M.chartTangentMap a x v) := by
  let c := chartAt (Model d) a
  have hc := (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
    (c.open_source.mem_nhds hx)
  have he : f =ᶠ[𝓝 x] (f ∘ c.symm) ∘ c := by
    filter_upwards [c.open_source.mem_nhds hx] with z hz
    simp only [Function.comp_apply, c.left_inv hz]
  have hd := mfderiv_comp x (hf.contMDiffAt.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  rw [scalarDerivative, he.mfderiv_eq, hd, mfderiv_eq_fderiv]
  rfl
end ExactLiouvilleComparison.MoserExactness
