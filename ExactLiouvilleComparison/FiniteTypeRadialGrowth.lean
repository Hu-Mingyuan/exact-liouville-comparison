import ExactLiouvilleComparison.FiniteTypeRadialRadius

noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.FiniteTypeRadial
variable {d : ℕ} {D : LiouvilleDomain d} {C : Completion D}
  {A : CompatibleStructure (completionReference C)}

/-- Package proved radius data, retaining the original primitive, J and g. -/
def Radius.toReference (Q : Radius C A) : RadialReference C.ambient.manifold where
  exactStructure := completionReference C
  compatible := A
  R := Q.R
  smooth_R := Q.smooth
  proper_R := Q.proper
  lower_R := Q.lower
  c := 1
  positive_c := by norm_num
  rstar := 2
  one_lt_rstar := by norm_num
  radial_identity := by
    intro x hx v
    simpa [completionReference] using Q.primitive_eq x hx v
  radial_bound := by
    intro x hx
    rw [one_mul, Q.dual_sq x hx]

/-- An explicit compact truncation transfers the estimate without changing B or C₀. -/
theorem growth_witness (Q : Radius C A)
    (T : ExactSymplecticStructure C.ambient.manifold) (B : AdmissibleGrowth 1)
    (C₀ t₀ : ℝ)
    (h : ∀ y t, t₀ ≤ t → A.inverseNorm T (C.endMap (y,t)) ≤ C₀ * B.B (Real.exp t)) :
    ∃ K : Set C.ambient.manifold.Point, IsCompact K ∧
      ∀ x, x ∉ K → A.inverseNorm T x ≤ C₀ * B.B (Q.R x) := by
  refine ⟨(farEnd C (max t₀ (Real.log 2)))ᶜ, compact_farEnd_compl C _, ?_⟩
  intro x hx
  have hx' : x ∈ farEnd C (max t₀ (Real.log 2)) := by simpa using hx
  obtain ⟨⟨y,t⟩, ht, rfl⟩ := hx'
  have ht₀ : t₀ ≤ t := (le_max_left _ _).trans ht.2.le
  have hlog : Real.log 2 ≤ t := (le_max_right _ _).trans ht.2.le
  rw [Q.end_eq y t ((Real.log_le_iff_le_exp (by norm_num)).mp hlog)]
  exact h y t ht₀

theorem growthWitnessTarget : GrowthWitnessTarget := by
  intro d D C A Q T B C₀ t₀ _ _ h
  exact growth_witness Q T B C₀ t₀ h

theorem growth (Q : Radius C A) (T : ExactSymplecticStructure C.ambient.manifold)
    (h : ∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
        A.inverseNorm T (C.endMap (y,t)) ≤ C₀ * B.B (Real.exp t)) :
    GrowthAtInfinity A T Q.R 1 := by
  obtain ⟨B,C₀,hC,t₀,_,h⟩ := h
  obtain ⟨K,hK,hbound⟩ := growth_witness Q T B C₀ t₀ h
  exact ⟨B,C₀,hC,K,hK,hbound⟩

end ExactLiouvilleComparison.FiniteTypeRadial
