import ExactLiouvilleComparison.NativeIntegrationStatement

/-! The two accepted constructions compose on the literal native quotient. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.NativeIntegration
open FiniteTypePresentation

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (α : IntrinsicLiouville.Form k M 1)
  (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
  (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
  (hout : LocalOutward α)

/-- Construct J on the adapter's quotient and feed it to that adapter's comparison. -/
theorem constructedComparison : ConstructedComparison α hα hnd hout := by
  let P := fromNative α hα hnd hout
  obtain ⟨A, ⟨cyl⟩⟩ := CylindricalCompatibility.existenceTarget (k + 1) P.domain (P.completed hα)
  exact ⟨P.identifications hα, A, ⟨cyl⟩, P.comparisonFor hα A cyl⟩

/-- Full prescribed contact-end extension on the same source-selected quotient. -/
theorem prescribedExtension : PrescribedExtension α hα hnd hout := by
  intro K
  exact CylindricalCompatibility.extension (fromNative α hα hnd hout |>.completed hα) K

/-- The original global theorem and all three applications remain available. -/
theorem manuscript : ManuscriptTarget := ManuscriptComparison.manuscriptTarget

/-- Completeness is carried by the prescribed all-real flows, as before. -/
theorem complete : CompleteLiouvilleComparisonTarget :=
  ManuscriptComparison.completeLiouvilleComparisonTarget

/-- The source adapter's positive-dimensional convention does not restrict
cylindrical existence for arbitrary accepted completions. -/
theorem allDimensions : CylindricalCompatibility.ExistenceTarget :=
  CylindricalCompatibility.existenceTarget

theorem everyPrescribedEnd : CylindricalCompatibility.ExtensionTarget :=
  CylindricalCompatibility.extensionTarget

example (D : LiouvilleDomain 0) (C : Completion D) :
    ∃ A : CompatibleStructure (completionReference C), Nonempty (CylindricalStructure C A) :=
  allDimensions 0 D C

example {d : ℕ} (D : LiouvilleDomain d) (C : Completion D) [IsEmpty D.domain.boundary.Point] :
    ∃ A : CompatibleStructure (completionReference C), Nonempty (CylindricalStructure C A) :=
  allDimensions d D C

end ExactLiouvilleComparison.NativeIntegration
#eval IO.println "NATIVE_INTEGRATION_CONSUMERS_COMPLETE"
