import ExactLiouvilleComparison.FirstPathFlowInputs
import ExactLiouvilleComparison.ODEScalarConfinement
import ExactLiouvilleComparison.ODEContinuationStatement

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathFlowChecks
variable {d : ℕ} {M : SmoothManifold d}

/-- Endpoint consumer of the actual given-growth first field, with the original
arbitrary compact exception. This asserts regularity data, not trajectories. -/
theorem exact_endpoints (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ∃ E : ℝ → (x : M.Point) → M.Tangent x,
      (∀ x, E 0 x = FirstPath.X P G T hw x 0 (by norm_num)) ∧
      (∀ x, E 1 x = FirstPath.X P G T hw x 1 (by norm_num)) ∧
      ∃ Ω : Set (ℝ × M.Point), IsOpen Ω ∧ parameterInterval ×ˢ univ ⊆ Ω ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
          (fun p : ℝ × M.Point => (⟨p.2, E p.1 p.2⟩ :
            TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω := by
  obtain ⟨E, heq, hE, _⟩ := FirstPathFlow.first_native_data P G T hw hC K hK hb
  exact ⟨E, heq parameterZero, heq parameterOne, hE⟩
end ExactLiouvilleComparison.FirstPathFlowChecks
