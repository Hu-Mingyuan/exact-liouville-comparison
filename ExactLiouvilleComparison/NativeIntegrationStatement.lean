import ExactLiouvilleComparison.FiniteTypePresentationConsumers
import ExactLiouvilleComparison.CylindricalCompatibilityFinalChecks
import ExactLiouvilleComparison.ManuscriptComparisonConsumers

/-! Source union: one native quotient, then constructed J, then arbitrary target. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.NativeIntegration
open FiniteTypePresentation

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The adapter's actual chosen quotient and its identifications precede the
constructed compatible structure. The target primitive is quantified last. -/
def ConstructedComparison (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : LocalOutward α) : Prop :=
  let P := fromNative α hα hnd hout
  let Q := P.completed hα
  P.Identifications hα ∧
    ∃ A : CompatibleStructure (completionReference Q),
      Nonempty (CylindricalStructure Q A) ∧
      ∀ T : ExactSymplecticStructure Q.ambient.manifold,
        WeaklyTames A T →
        (∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
          ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
            A.inverseNorm T (Q.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) →
        FiniteTypeComparison.NativeConclusion Q.ambient.manifold T.primitive Q.ambient.primitive

/-- Every prescribed smooth contact end extends on the very same quotient.
`Extends` is the accepted full formula for all t ≥ 0, including the seam. -/
def PrescribedExtension (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : LocalOutward α) : Prop :=
  let P := fromNative α hα hnd hout
  ∀ K : CylindricalCompatibility.ContactData P.domain,
    ∃ A : CompatibleStructure (completionReference (P.completed hα)),
      CylindricalCompatibility.Extends (P.completed hα) K A

end ExactLiouvilleComparison.NativeIntegration
