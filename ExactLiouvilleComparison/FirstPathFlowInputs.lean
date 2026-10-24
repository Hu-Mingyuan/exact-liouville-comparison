import ExactLiouvilleComparison.ODEIntervalRegularity

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- Actual native ODE inputs, for the given arbitrary growth witness and compact exception. -/
theorem first_native_data (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ∃ E : ℝ → (x : M.Point) → M.Tangent x,
      (∀ t : Parameter, ∀ x, E t.val x = FirstPath.X P G T hw x t.val t.property.1) ∧
      (∃ Ω : Set (ℝ × M.Point), IsOpen Ω ∧ parameterInterval ×ˢ univ ⊆ Ω ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
          (fun p : ℝ × M.Point => (⟨p.2, E p.1 p.2⟩ :
            TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω) ∧
      ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (FirstPath.exhaustion P G) ∧
      IsProperMap (FirstPath.exhaustion P G) ∧
      BddBelow (range (FirstPath.exhaustion P G)) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ parameterInterval, ∀ x,
        |M.scalarDerivative (FirstPath.exhaustion P G) x (E t x)| ≤ D := by
  obtain ⟨E, heq, hE⟩ := ODE.native_open_of_interval_family _
    (MoserRegularity.first_intervalSmooth P G T hw)
  obtain ⟨D, hD, hbD⟩ := MoserRegularity.first_global P G T hw hC K hK hb
  refine ⟨E, (fun t x => congrFun (heq t) x), hE, FirstPath.exhaustion_smooth P G,
    FirstPath.exhaustion_proper P G, FirstPath.exhaustion_bddBelow P G, D, hD, ?_⟩
  intro t ht x
  simpa only [heq ⟨t, ht⟩] using hbD ⟨t, ht⟩ x

/-- The unchanged existential growth hypothesis supplies the same coefficient witness
to both the scalar estimate and the native open-neighborhood bridge. -/
theorem first_growth_data (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (hg : GrowthAtInfinity P.compatible T P.R 1) :
    ∃ (G : AdmissibleGrowth 1) (E : ℝ → (x : M.Point) → M.Tangent x),
      (∀ t : Parameter, ∀ x, E t.val x = FirstPath.X P G T hw x t.val t.property.1) ∧
      (∃ Ω : Set (ℝ × M.Point), IsOpen Ω ∧ parameterInterval ×ˢ univ ⊆ Ω ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
          (fun p : ℝ × M.Point => (⟨p.2, E p.1 p.2⟩ :
            TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω) ∧
      ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (FirstPath.exhaustion P G) ∧
      IsProperMap (FirstPath.exhaustion P G) ∧
      BddBelow (range (FirstPath.exhaustion P G)) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ parameterInterval, ∀ x,
        |M.scalarDerivative (FirstPath.exhaustion P G) x (E t x)| ≤ D := by
  obtain ⟨G, _, hp, hl, D, hD, hb⟩ := MoserRegularity.first_growth_consumer P T hw hg
  obtain ⟨E, heq, hE⟩ := ODE.native_open_of_interval_family _
    (MoserRegularity.first_intervalSmooth P G T hw)
  refine ⟨G, E, (fun t x => congrFun (heq t) x), hE,
    FirstPath.exhaustion_smooth P G, hp, hl, D, hD, ?_⟩
  intro t ht x
  simpa only [heq ⟨t, ht⟩] using hb ⟨t, ht⟩ x
end ExactLiouvilleComparison.FirstPathFlow
