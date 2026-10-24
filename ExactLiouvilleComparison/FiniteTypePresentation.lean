import ExactLiouvilleComparison.FiniteTypePresentationStatement

/-! Construct the native quotient, prove its source identifications, and consume
the existing finite-type comparison on that very quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology FsFltz.Geometry FsFltz.Geometry.SmoothManifold
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace ExactLiouvilleComparison.FiniteTypePresentation

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Retain the actual quotient witnesses used by `exists_completion_from_native`,
including the native boundary identification that its existential result hides. -/
theorem exists_quotientData (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : LocalOutward α) : Nonempty (QuotientData α) := by
  obtain ⟨C, δ, hδ, hemb, hC, hb, hi, hz, L, _, hn, hc, hglobal, hf, hnf, _⟩ :=
    IntrinsicLiouville.exists_liouvilleStructure_from_native α hα hnd hout
  exact ⟨⟨C, δ, hδ, hemb, hC, hb, hi, hz, L, hn, hc, hglobal, hf, hnf⟩⟩

/-- One quotient is selected solely from the source domain, before J or λ₁. -/
def fromNative (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : LocalOutward α) : QuotientData α :=
  Classical.choice (exists_quotientData α hα hnd hout)

namespace QuotientData
variable {α : IntrinsicLiouville.Form k M 1} (P : QuotientData α)
  (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)

/-- Full source, field, boundary, and attached-end preservation are consequences
of the already constructed quotient. No geometric preservation law is assumed. -/
theorem identifications : P.Identifications hα := by
  let := completionChartedSpace P.positive P.collar P.embedding P.boundary P.zero
  refine ⟨contMDiff_original P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero,
    isClosedEmbedding_original P.positive _ P.embedding,
    bijective_mfderiv_original P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero,
    (compactDomain_carrier P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero).symm,
    compactDomain_frontier P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero,
    fun _ => rfl, congrFun P.native_primitive, ?_,
    compactDomain_boundaryInclusion P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero,
    boundaryForm_eq_restrictForm P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero
      α P.liouville P.native_primitive, ?_,
    completion_original_end_primitive P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero
      α hα P.liouville P.nondegenerate P.cylinder_primitive P.native_primitive⟩
  · intro x
    exact (congrFun P.canonical_field (P.nativeIn x)).symm.trans (P.native_field x)
  · intro b t ht
    exact boundaryOrbitMap_eq_outwardEndMap P.positive P.collar P.embedding P.smooth P.boundary
      P.inverse P.zero α hα P.liouville P.nondegenerate P.cylinder_primitive
      (completeFlow P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero
        α hα P.liouville P.nondegenerate P.cylinder_primitive) (b, t) ht

/-- Apply the accepted comparison theorem without altering A, its metric/norms,
the weak-taming premise or the inverse-norm end-growth premise. -/
theorem comparisonFor : P.ComparisonFor hα := by
  intro A cyl T hw hg
  exact FiniteTypeComparison.native_of_exactComparison
    (FiniteTypeComparison.finiteTypeTarget (k + 1) P.domain (P.completed hα) A cyl T hw hg)

end QuotientData

/-- The bounded source-presentation target is proved, not merely specified. -/
theorem nativeTarget (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) : NativeTarget α hα := by
  intro hnd hout
  let P := fromNative α hα hnd hout
  exact ⟨P, P.identifications hα, P.comparisonFor hα⟩

/-- Direct source-data consumer on the selected quotient. -/
theorem comparisonFromNative (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : LocalOutward α) : (fromNative α hα hnd hout).ComparisonFor hα :=
  (fromNative α hα hnd hout).comparisonFor hα

end ExactLiouvilleComparison.FiniteTypePresentation
