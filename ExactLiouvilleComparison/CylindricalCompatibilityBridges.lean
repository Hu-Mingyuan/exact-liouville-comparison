import ExactLiouvilleComparison.CylindricalCompatibilityStatement
import ExactLiouvilleComparison.FiniteTypeComparison

/-! Bridges for the reviewed cylindrical construction contract. These do not
assert the outstanding existence or extension theorem. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {d : ℕ} {D : LiouvilleDomain d} {C : Completion D}

/-- The full prescribed end formula supplies every field of the existing
cylindrical interface, without changing the accepted comparison statement. -/
def Extends.cylindrical {P : ContactData D}
    {A : CompatibleStructure (completionReference C)} (h : Extends C P A) :
    CylindricalStructure C A where
  reeb := P.reeb
  contactJ := P.J
  reeb_normalized := P.normalized
  reeb_kernel := P.kernel
  contactJ_reeb := P.annihilate_reeb
  contactJ_horizontal := P.horizontal
  cylindrical := h

/-- The constructed witness retains the prescribed Reeb field literally. -/
theorem Extends.cylindrical_reeb {P : ContactData D}
    {A : CompatibleStructure (completionReference C)} (h : Extends C P A) :
    h.cylindrical.reeb = P.reeb := rfl

/-- The constructed witness retains the prescribed contact endomorphism literally. -/
theorem Extends.cylindrical_contactJ {P : ContactData D}
    {A : CompatibleStructure (completionReference C)} (h : Extends C P A) :
    h.cylindrical.contactJ = P.J := rfl

/-- An extended prescribed structure consumes the already proved comparison
with exactly its original weak-taming and existential end-growth premises. -/
theorem comparison_of_extends {P : ContactData D}
    {A : CompatibleStructure (completionReference C)} (h : Extends C P A)
    (T : ExactSymplecticStructure C.ambient.manifold)
    (htame : WeaklyTames A T)
    (hgrowth : ∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
        A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) :
    ExactComparison C.ambient.manifold T.primitive C.ambient.primitive :=
  FiniteTypeComparison.finiteTypeTarget d D C A h.cylindrical T htame hgrowth

/-- Assembly only: contact existence and prescribed extension are separate,
still indispensable proof inputs to this implication. -/
theorem existence_of_contact_and_extension
    (hc : ContactExistenceTarget) (he : ExtensionTarget) : ExistenceTarget := by
  intro d D C
  obtain ⟨P⟩ := hc d D C
  obtain ⟨A, hA⟩ := he d D C P
  exact ⟨A, ⟨hA.cylindrical⟩⟩

/-- Assembly only: once existence is proved, the choice precedes the arbitrary
new exact symplectic primitive. No new completeness or growth premise is added. -/
theorem consumer_of_existence (h : ExistenceTarget) : ConsumerTarget := by
  intro d D C
  obtain ⟨A, ⟨hA⟩⟩ := h d D C
  exact ⟨A, ⟨hA⟩, FiniteTypeComparison.finiteTypeTarget d D C A hA⟩

end ExactLiouvilleComparison.CylindricalCompatibility
