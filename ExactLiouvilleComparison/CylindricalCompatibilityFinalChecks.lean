import ExactLiouvilleComparison.CylindricalCompatibility

/-! Native consumers of the constructed reference, including degenerate scope. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.FinalChecks

example (d : ℕ) (D : LiouvilleDomain d) (C : Completion D) :
    ∃ A : CompatibleStructure (completionReference C), Nonempty (CylindricalStructure C A) :=
  existenceTarget d D C

example (D : LiouvilleDomain 0) (C : Completion D) :
    ∃ A : CompatibleStructure (completionReference C), Nonempty (CylindricalStructure C A) :=
  existenceTarget 0 D C

example {d : ℕ} (D : LiouvilleDomain d) (C : Completion D) [IsEmpty D.domain.boundary.Point] :
    ∃ A : CompatibleStructure (completionReference C), Nonempty (CylindricalStructure C A) :=
  existenceTarget d D C

example {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) (P : ContactData D) :
    ∃ A : CompatibleStructure (completionReference C), Extends C P A := extension C P

/-- The constructed choice is made before T, and the native diffeomorphism,
isotopy and exact primitive conclusion use precisely the original hypotheses. -/
theorem native_consumer (d : ℕ) (D : LiouvilleDomain d) (C : Completion D) :
    ∃ A : CompatibleStructure (completionReference C),
      Nonempty (CylindricalStructure C A) ∧
      ∀ T : ExactSymplecticStructure C.ambient.manifold,
        WeaklyTames A T →
        (∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
          ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
            A.inverseNorm T (C.endMap (y,t)) ≤ C₀ * B.B (Real.exp t)) →
        FiniteTypeComparison.NativeConclusion C.ambient.manifold T.primitive C.ambient.primitive := by
  obtain ⟨A,hc,h⟩ := consumerTarget d D C
  exact ⟨A,hc,fun T ht hg => FiniteTypeComparison.native_of_exactComparison (h T ht hg)⟩

end ExactLiouvilleComparison.CylindricalCompatibility.FinalChecks
#eval IO.println "CYLINDRICAL_COMPATIBILITY_FINAL_CONSUMERS_COMPLETE"
