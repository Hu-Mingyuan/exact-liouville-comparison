import ExactLiouvilleComparison.FiniteTypeComparisonStatement

/-! The finite-type corollary on the original completion and metric. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FiniteTypeComparison
variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
  (A : CompatibleStructure (completionReference C)) (cyl : CylindricalStructure C A)

theorem reference_exactStructure :
    (FiniteTypeRadial.reference C A cyl).exactStructure = completionReference C := rfl

theorem reference_compatible :
    (FiniteTypeRadial.reference C A cyl).compatible = A := rfl

theorem reference_primitive :
    (FiniteTypeRadial.reference C A cyl).exactStructure.primitive = C.ambient.primitive := rfl

theorem reference_constants :
    (FiniteTypeRadial.reference C A cyl).c = 1 ∧
    (FiniteTypeRadial.reference C A cyl).rstar = 2 := ⟨rfl, rfl⟩

theorem reference_inner (x : C.ambient.manifold.Point)
    (v w : C.ambient.manifold.Tangent x) :
    (FiniteTypeRadial.reference C A cyl).compatible.g.inner x v w = A.g.inner x v w := rfl

theorem reference_dualNorm (x : C.ambient.manifold.Point)
    (l : C.ambient.manifold.Tangent x →L[ℝ] ℝ) :
    (FiniteTypeRadial.reference C A cyl).compatible.dualNorm x l = A.dualNorm x l := rfl

theorem reference_inverseNorm (T : ExactSymplecticStructure C.ambient.manifold)
    (x : C.ambient.manifold.Point) :
    (FiniteTypeRadial.reference C A cyl).compatible.inverseNorm T x = A.inverseNorm T x := rfl

theorem reference_weaklyTames_iff (T : ExactSymplecticStructure C.ambient.manifold) :
    WeaklyTames (FiniteTypeRadial.reference C A cyl).compatible T ↔ WeaklyTames A T := Iff.rfl

/-- Apply the delivered unconditional main theorem and end-growth bridge.
All data in the result reduce to the original completion, primitive and A. -/
theorem finiteTypeTarget : FiniteTypeTarget := by
  intro d D C A cyl T hw hg
  exact MainComparison.mainTarget d C.ambient.manifold
    (FiniteTypeRadial.reference C A cyl) T hw (FiniteTypeRadial.reference_growth C A cyl T hg)

/-- Expose witnesses already proved by the comparison; no witness is an input. -/
theorem native_of_exactComparison {d : ℕ} {M : SmoothManifold d} {source target : M.Form 1}
    (h : ExactComparison M source target) : NativeConclusion M source target := by
  obtain ⟨F, ⟨H, h0, h1, hs, hi⟩, h, hh, hp, hd⟩ := h
  exact ⟨F, h, H, h0, h1, hs, hi, hh, hp, hd⟩

include cyl in
/-- Same original existential end-growth premise, with the native output unfolded. -/
theorem nativeConclusion (T : ExactSymplecticStructure C.ambient.manifold)
    (hw : WeaklyTames A T)
    (hg : ∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
        A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) :
    NativeConclusion C.ambient.manifold T.primitive C.ambient.primitive :=
  native_of_exactComparison (finiteTypeTarget d D C A cyl T hw hg)

end ExactLiouvilleComparison.FiniteTypeComparison
