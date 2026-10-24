import ExactLiouvilleComparison.MoserExactness
import ExactLiouvilleComparison.FirstPathExactnessPullback

/-! Unconditional first-path exactness with the delivered coefficient, field,
constructed evolution, and literal globally smooth integral gauge. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathExactness
variable {d : ℕ} {M : SmoothManifold d}

/-- The accepted first-path target, without any added analytic or completeness premise. -/
theorem firstPathExactness : Target (M := M) := by
  intro P G T hw C hC K hK hb
  exact MoserExactness.moserExactness _ (primitive_smoothFamily P G T)
    (MoserRegularity.firstField P G T hw) (field_smooth P G T hw)
    (field_equation P G T hw) (FirstPathFlow.evolution P G T hw hC K hK hb)

/-- The forward endpoint compares λ + k(R)β to λ, in the original native
ExactComparison interface, retaining the actual evolution isotopy and gauge. -/
theorem exactComparison (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ExactComparison M (primitive P G T 1) T.primitive := by
  let E := FirstPathFlow.evolution P G T hw hC K hK hb
  obtain ⟨_, hs, hp, he⟩ := firstPathExactness P G T hw C hC K hK hb
  refine ⟨E.map parameterZero parameterOne, E.isotopy parameterOne,
    MoserExactness.gauge (primitive P G T) E, hs, ?_, ?_⟩
  · simpa only [primitive, zero_smul, add_zero] using hp
  · simpa only [primitive, zero_smul, add_zero] using he

end ExactLiouvilleComparison.FirstPathExactness
