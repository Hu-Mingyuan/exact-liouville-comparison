import ExactLiouvilleComparison.FirstPathFlowStatement

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Retain the coefficient neighborhoods to construct a native open neighborhood. -/
theorem native_open_of_chart_family
    (Z : ℝ → (x : M.Point) → M.Tangent x) (hZ : M.IsSmoothVectorFieldFamily Z) :
    ∃ Ω : Set (ℝ × M.Point), IsOpen Ω ∧ parameterInterval ×ˢ univ ⊆ Ω ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ :
          TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω := by
  classical
  choose U hU hsub hdiff using hZ
  let V : M.Point → Set (ℝ × M.Point) := fun a =>
    (univ ×ˢ (chartAt (Model d) a).source) ∩
      (fun p : ℝ × M.Point => (p.1, chartAt (Model d) a p.2)) ⁻¹' U a
  have hopen (a : M.Point) : IsOpen (V a) := by
    have hc : ContinuousOn (fun p : ℝ × M.Point => (p.1, chartAt (Model d) a p.2))
        (univ ×ˢ (chartAt (Model d) a).source) :=
      continuousOn_fst.prodMk ((chartAt (Model d) a).continuousOn.comp continuousOn_snd
        (fun _ hp => hp.2))
    exact hc.isOpen_inter_preimage
      (isOpen_univ.prod (chartAt (Model d) a).open_source) (hU a)
  refine ⟨⋃ a, V a, isOpen_iUnion hopen, ?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨ht, _⟩
    apply mem_iUnion.mpr
    refine ⟨x, ⟨mem_univ _, mem_chart_source _ _⟩, ?_⟩
    exact hsub x ⟨ht, (chartAt (Model d) x).map_source (mem_chart_source _ _)⟩
  · intro p hp
    obtain ⟨a, ha⟩ := mem_iUnion.mp hp
    exact (M.contMDiffAt_familySection_of_chart Z a p ha.1.2
      ((hdiff a).contDiffAt ((hU a).mem_nhds ha.2))).contMDiffWithinAt

/-- Preserve one extension and exact agreement at both interval endpoints. -/
theorem native_open_of_interval_family
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) :
    ∃ E : ℝ → (x : M.Point) → M.Tangent x,
      (∀ t : Parameter, E t.val = Z t) ∧
      ∃ Ω : Set (ℝ × M.Point), IsOpen Ω ∧ parameterInterval ×ˢ univ ⊆ Ω ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
          (fun p : ℝ × M.Point => (⟨p.2, E p.1 p.2⟩ :
            TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω := by
  obtain ⟨E, hE, heq⟩ := hZ
  exact ⟨E, heq, native_open_of_chart_family E hE⟩

/-- The native nonautonomous equation implies the actual ODE in any valid chart,
including within derivatives at the closed parameter endpoints. -/
theorem chart_hasDerivWithinAt
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    {γ : ℝ → M.Point} {J : Set ℝ} (hγ : FirstPathFlow.IsSolution Z γ J)
    {t : ℝ} (ht : t ∈ J) (hi : t ∈ parameterInterval)
    (a : M.Point) (ha : γ t ∈ (chartAt (Model d) a).source) :
    HasDerivWithinAt (fun u => chartAt (Model d) a (γ u))
      (M.chartTangentMap a (γ t) (Z ⟨t, hi⟩ (γ t))) J t := by
  have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt ha
  have hd := hc.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ.2 t ht hi)
  have hr := (hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp hd).hasDerivWithinAt
  apply hr.congr_deriv
  change M.chartTangentMap a (γ t) ((1 : ℝ) • Z ⟨t, hi⟩ (γ t)) = _
  rw [one_smul]
end ExactLiouvilleComparison.ODE
