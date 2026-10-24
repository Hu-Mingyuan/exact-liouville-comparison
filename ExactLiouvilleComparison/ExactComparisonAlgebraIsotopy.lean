import ExactLiouvilleComparison.ExactComparisonAlgebraStatement

/-! Structural laws for the unchanged smooth identity-isotopy predicate. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison
namespace SmoothlyIsotopicToIdentity
variable {d : ℕ} {M : SmoothManifold d}

/-- The constant identity family is jointly smooth in both directions. -/
theorem refl (M : SmoothManifold d) :
    SmoothlyIsotopicToIdentity M (Diffeomorph.refl _ _ ∞) := by
  refine ⟨fun _ => Diffeomorph.refl _ _ ∞, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · exact contMDiff_snd.contMDiffOn
  · exact contMDiff_snd.contMDiffOn

/-- Invert each member of the supplied isotopy. -/
theorem symm {F : M.SmoothEquiv M} (hF : SmoothlyIsotopicToIdentity M F) :
    SmoothlyIsotopicToIdentity M F.symm := by
  obtain ⟨H, h0, h1, hH, hHi⟩ := hF
  have h0' : H 0 = Diffeomorph.refl _ _ ∞ := Diffeomorph.ext h0
  have h1' : H 1 = F := Diffeomorph.ext h1
  refine ⟨fun t => (H t).symm, ?_, ?_, hHi, hH⟩
  · intro x
    simp [h0']
  · intro x
    simp only [h1']

/-- Pointwise composition of isotopies, in native `Diffeomorph.trans` order.
The inverse family has the reversed order. -/
theorem trans {F G : M.SmoothEquiv M}
    (hF : SmoothlyIsotopicToIdentity M F) (hG : SmoothlyIsotopicToIdentity M G) :
    SmoothlyIsotopicToIdentity M (F.trans G) := by
  obtain ⟨H, hH0, hH1, hH, hHi⟩ := hF
  obtain ⟨K, hK0, hK1, hK, hKi⟩ := hG
  refine ⟨fun t => (H t).trans (K t), ?_, ?_, ?_, ?_⟩
  · intro x
    change K 0 (H 0 x) = x
    rw [hH0, hK0]
  · intro x
    change K 1 (H 1 x) = G (F x)
    rw [hH1, hK1]
  · exact hK.comp (contMDiff_fst.contMDiffOn.prodMk hH)
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  · exact hHi.comp (contMDiff_fst.contMDiffOn.prodMk hKi)
      (fun p hp => ⟨hp.1, mem_univ _⟩)

end SmoothlyIsotopicToIdentity

namespace ExactComparisonAlgebra

theorem isotopyLaws (M : SmoothManifold d) : IsotopyLawsStatement M :=
  ⟨SmoothlyIsotopicToIdentity.refl M,
    fun _ h => h.symm, fun _ _ hF hG => hG.trans hF⟩

end ExactComparisonAlgebra
end ExactLiouvilleComparison
