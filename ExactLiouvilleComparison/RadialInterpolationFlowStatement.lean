import ExactLiouvilleComparison.FirstPathFlowStatement

/-! Radial interpolation flow contract. Targets are specifications, not existence proofs. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.RadialInterpolationFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- Lemma `lem:bridge`, retaining degenerate d sigma, arbitrary coefficient growth,
closed endpoints and every initial time. The field is the literal accepted inverse
contraction, and Evolution is output data, never an existence hypothesis. -/
def Target : Prop :=
  ∀ (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar),
    (∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r) →
    Tendsto (fun r => r * q₀.rho r) atTop atTop →
    ∀ (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
      (hw : RadialInterpolation.WeakDifferential (P := P) σ),
    Nonempty (FirstPathFlow.Evolution (fun t x =>
      RadialInterpolation.vector (RadialInterpolation.coefficient q₀ q₁ t.val t.property)
        σ hσ hw (RadialInterpolation.delta q₀ q₁) x))
end ExactLiouvilleComparison.RadialInterpolationFlow
