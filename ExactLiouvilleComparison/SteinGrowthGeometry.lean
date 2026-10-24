import ExactLiouvilleComparison.SteinGrowth

/-! Enlarge only the compact exception; the metric and inverse norm stay fixed. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison.SteinGrowth

/-- Properness plus the lower bound makes the whole sublevel compact. -/
theorem isCompact_sublevel {X : Type*} [TopologicalSpace X]
    {R : X → ℝ} (hR : IsProperMap R) (hlower : ∀ x, 1 ≤ R x) (b : ℝ) :
    IsCompact {x | R x ≤ b} := by
  have heq : {x | R x ≤ b} = R ⁻¹' Icc 1 b := by
    ext x
    exact ⟨fun hx => ⟨hlower x, hx⟩, fun hx => hx.2⟩
  rw [heq]
  exact hR.isCompact_preimage isCompact_Icc

/-- A concrete compact enlargement, independent of the symplectic data. -/
def enlargedException {X : Type*} (R : X → ℝ) (K : Set X) : Set X :=
  K ∪ {x | R x ≤ Real.exp 1 + 2}

theorem enlargedException_compact {X : Type*} [TopologicalSpace X]
    {R : X → ℝ} (hR : IsProperMap R) (hlower : ∀ x, 1 ≤ R x)
    {K : Set X} (hK : IsCompact K) : IsCompact (enlargedException R K) :=
  hK.union (isCompact_sublevel hR hlower _)

theorem subset_enlargedException {X : Type*} (R : X → ℝ) (K : Set X) :
    K ⊆ enlargedException R K := subset_union_left

/-- Preserve the exact g-dual to g operator norm and the original constant C. -/
theorem estimate_outside_enlarged {d : ℕ} {M : SmoothManifold d}
    {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (T : ExactSymplecticStructure M) (R : M.Point → ℝ)
    (B : AdmissibleGrowth (Real.exp 1)) (C : ℝ) (K : Set M.Point)
    (hbound : ∀ x, x ∉ K → A.inverseNorm T x ≤ C * B.B (R x)) :
    ∀ x, x ∉ enlargedException R K → A.inverseNorm T x ≤ C * (extend B).B (R x) := by
  intro x hx
  have hK : x ∉ K := fun hk => hx (Or.inl hk)
  have hr : Real.exp 1 + 2 < R x := lt_of_not_ge (fun hr => hx (Or.inr hr))
  rw [extend_eq B hr.le]
  exact hbound x hK

theorem witnessTarget : WitnessTarget := by
  intro d M S A T R hR hlower B C _hC K hK hbound
  exact ⟨extend B, enlargedException R K, enlargedException_compact hR hlower hK,
    subset_enlargedException R K, fun _ hr => extend_eq B hr,
    estimate_outside_enlarged A T R B C K hbound⟩

/-- Convert the unchanged growth predicate on any proper radius bounded below by 1. -/
theorem growthAtInfinity {d : ℕ} {M : SmoothManifold d}
    {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (T : ExactSymplecticStructure M) (R : M.Point → ℝ)
    (hR : IsProperMap R) (hlower : ∀ x, 1 ≤ R x)
    (h : GrowthAtInfinity A T R (Real.exp 1)) : GrowthAtInfinity A T R 1 := by
  obtain ⟨B, C, hC, K, hK, hbound⟩ := h
  exact ⟨extend B, C, hC, enlargedException R K,
    enlargedException_compact hR hlower hK,
    estimate_outside_enlarged A T R B C K hbound⟩

theorem growthTarget : GrowthTarget := by
  intro d M S A T R hR hlower h
  exact growthAtInfinity A T R hR hlower h

end ExactLiouvilleComparison.SteinGrowth
